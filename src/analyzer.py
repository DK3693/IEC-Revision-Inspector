# -*- coding: utf-8 -*-
"""
IEC Revision Analyzer V7.0 - FOREWORD-first, structure-diff hybrid.

Role split (see docs/ARCHITECTURE.md for the evidence behind each rule):
  CODE  : PDF text extraction, running header/footer removal, de-hyphenation, logical structure
          (clauses / terminological entries / notes / sources / captions), OLD<->NEW section and
          paragraph alignment, word-level diff hunks, rule-based editorial tagging, geometry, report.
  LLM   : FOREWORD revision-list parsing (what the authors declare as meaningful change), and per-hunk
          judgement: did the meaning change, which FOREWORD item it belongs to, Korean explanation.
  VLM   : fixed-schema comparison of formula / figure crops that are candidates of a FOREWORD item with a region (optional).

Nothing in this file is specific to one IEC publication. Structural rules come from ISO/IEC
Directives Part 2 (clause numbering, annexes, figures/tables) and ISO 10241-1 (terminological
entries: term line, "Note n to entry", "[SOURCE: ...]"). Document-dependent quantities (header
positions, body font size, similarity thresholds) are calibrated from the documents themselves.
"""
from __future__ import annotations

import base64
import difflib
import html
import json
import math
import os
import queue
import re
import threading
import time
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

try:
    import fitz  # PyMuPDF
except Exception:
    fitz = None


APP_VERSION = "7.0.0-hybrid-structural-diff"
OLLAMA_DEFAULT_URL = "http://127.0.0.1:11434"
DEFAULT_NUM_CTX = 32768
DEFAULT_NUM_PREDICT = 8192
DEFAULT_VISION_NUM_PREDICT = 2048

_ACTIVE_LOG_PATH: Optional[Path] = None
_LOG_LOCK = threading.Lock()
_LLM_CALL_SEQ = 0
_LLM_CALL_LOCK = threading.Lock()
_LAST_TEXT_RESPONSE_META: dict = {}

# ------------------------------------------------------------------
# Calibration constants. Each one is either a published convention or a
# conservative starting value that the code re-estimates from the documents.
# ------------------------------------------------------------------
# Running headers/footers live in the outer bands of the page (Lin 2002; Dejean & Meunier 2006 use
# position + repetition across pages). 15 % of page height per band is generous for A4 standards.
HEADER_FOOTER_BAND_RATIO = 0.15
# A header/footer signature must repeat on at least this fraction of pages (and >= 3 pages).
HEADER_FOOTER_MIN_PAGE_RATIO = 0.25
# A page is a table of contents when at least this fraction of its lines end with dot leaders + number.
TOC_LINE_RATIO = 0.35
# Language identification by common short words (Grefenstette 1995), English vs French page. The word lists are
# the public Snowball stop-word lists (snowballstem.org/algorithms/english/stop.txt and .../french/stop.txt,

# ("me", "on") count for neither language. The French one-letter entries are elision forms (c' d' j' l' m' n' s' t',
# as the list itself annotates them) and are counted only when written with their apostrophe, so formula symbols
# t, s, n, ... in English text are not read as French.
EN_STOPWORDS = frozenset([
    'a', 'about', 'above', 'after', 'again', 'against', 'all', 'am', 'an', 'and', 'any', 'are', "aren't", 'as',
    'at', 'be', 'because', 'been', 'before', 'being', 'below', 'between', 'both', 'but', 'by', "can't", 'cannot',
    'could', "couldn't", 'did', "didn't", 'do', 'does', "doesn't", 'doing', "don't", 'down', 'during', 'each',
    'few', 'for', 'from', 'further', 'had', "hadn't", 'has', "hasn't", 'have', "haven't", 'having', 'he', "he'd",
    "he'll", "he's", 'her', 'here', "here's", 'hers', 'herself', 'him', 'himself', 'his', 'how', "how's", 'i',
    "i'd", "i'll", "i'm", "i've", 'if', 'in', 'into', 'is', "isn't", 'it', "it's", 'its', 'itself', "let's",
    'me', 'more', 'most', "mustn't", 'my', 'myself', 'no', 'nor', 'not', 'of', 'off', 'on', 'once', 'only', 'or',
    'other', 'ought', 'our', 'ours', 'ourselves', 'out', 'over', 'own', 'same', "shan't", 'she', "she'd",
    "she'll", "she's", 'should', "shouldn't", 'so', 'some', 'such', 'than', 'that', "that's", 'the', 'their',
    'theirs', 'them', 'themselves', 'then', 'there', "there's", 'these', 'they', "they'd", "they'll", "they're",
    "they've", 'this', 'those', 'through', 'to', 'too', 'under', 'until', 'up', 'very', 'was', "wasn't", 'we',
    "we'd", "we'll", "we're", "we've", 'were', "weren't", 'what', "what's", 'when', "when's", 'where', "where's",
    'which', 'while', 'who', "who's", 'whom', 'why', "why's", 'with', "won't", 'would', "wouldn't", 'you',
    "you'd", "you'll", "you're", "you've", 'your', 'yours', 'yourself', 'yourselves',
])
FR_STOPWORDS = frozenset([
    'ai', 'aie', 'aient', 'aies', 'ait', 'au', 'aurai', 'auraient', 'aurais', 'aurait', 'aurez', 'auriez',
    'aurions', 'aurons', 'auront', 'aux', 'avaient', 'avais', 'avait', 'avec', 'avez', 'aviez', 'avons', 'ayant',
    'ayez', 'ayons', 'c', 'ce', 'ceci', 'cela', 'celà', 'ces', 'cet', 'cette', 'd', 'dans', 'de', 'des', 'du',
    'elle', 'en', 'es', 'et', 'eu', 'eue', 'eues', 'eurent', 'eus', 'eusse', 'eussent', 'eusses', 'eussiez',
    'eussions', 'eut', 'eux', 'eûmes', 'eût', 'eûtes', 'furent', 'fus', 'fusse', 'fussent', 'fusses', 'fussiez',
    'fussions', 'fut', 'fûmes', 'fûtes', 'ici', 'il', 'ils', 'j', 'je', 'l', 'la', 'le', 'les', 'leur', 'leurs',
    'lui', 'm', 'ma', 'mais', 'me', 'mes', 'moi', 'mon', 'même', 'n', 'ne', 'nos', 'notre', 'nous', 'on', 'ont',
    'ou', 'par', 'pas', 'pour', 'qu', 'que', 'quel', 'quelle', 'quelles', 'quels', 'qui', 's', 'sa', 'sans',
    'se', 'sera', 'serai', 'seraient', 'serais', 'serait', 'seras', 'serez', 'seriez', 'serions', 'serons',
    'seront', 'ses', 'soi', 'soient', 'sois', 'soit', 'sont', 'soyez', 'soyons', 'suis', 'sur', 't', 'ta', 'te',
    'tes', 'toi', 'ton', 'tu', 'un', 'une', 'vos', 'votre', 'vous', 'y', 'à', 'étaient', 'étais', 'était',
    'étant', 'étiez', 'étions', 'étée', 'étées', 'êtes',
])
FR_ELISION_RE = re.compile(r"\b[cdjlmnst]'(?=[a-z\u00c0-\u00ff\u0153])")
# Paragraph alignment: the similarity below which an aligned pair is better explained as delete + insert is
# calibrated on each document pair (calibrate_paragraph_threshold). This value is only the fallback for a pair
# that offers no calibration sample, and the log says when it was used.
PARAGRAPH_MATCH_THRESHOLD = 0.40
# Section alignment stage C threshold floor; the real value is calibrated per document pair.
SECTION_SIMILARITY_FLOOR = 0.30
# LLM batch sizing: keep one classification call well inside num_ctx.
CLASSIFY_BATCH_CHARS = 9000
# What the LLM reads is never cut silently: a hunk may use a whole batch, longer texts carry a TRUNCATED marker.
TRIAGE_HUNK_CHARS = 14000       # = TRIAGE_BATCH_CHARS: a hunk longer than a batch is the only member of its batch
EXPLAIN_DIFF_CHARS = 11000      # = EXPLAIN_BATCH_CHARS
CONTEXT_HUNK_CHARS = 10000
CONTEXT_SECTION_CHARS = 10000
CONTEXT_REF_CHARS = 6000
CONTEXT_TOTAL_CHARS = 48000     # ~18k tokens of a 32k context, leaving room for the system prompt and the answer
CLASSIFY_BATCH_MAX_HUNKS = 12
EDITORIAL_BATCH_MAX_HUNKS = 30
AGENT_PROMPT_CHARS_PER_TOKEN = 2.6
AGENT_OUTPUT_RESERVE_TOKENS = 4096
FOREWORD_MAX_PAGES = 12


def _log_event(event: str, **fields) -> None:
    if _ACTIVE_LOG_PATH is None:
        return
    row = {"timestamp": datetime.now().isoformat(timespec="milliseconds"), "event": event, **fields}
    try:
        line = json.dumps(row, ensure_ascii=False, default=str)
        with _LOG_LOCK:
            _ACTIVE_LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
            with _ACTIVE_LOG_PATH.open("a", encoding="utf-8") as f:
                f.write(line + "\n")
    except Exception:
        pass


def _next_llm_call_id() -> int:
    global _LLM_CALL_SEQ
    with _LLM_CALL_LOCK:
        _LLM_CALL_SEQ += 1
        return _LLM_CALL_SEQ


# ============================================================
# Basic helpers
# ============================================================

def clean(s: str) -> str:
    s = str(s or "").replace("­", "").replace("﻿", "")
    s = re.sub(r"[ \t]+", " ", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", clean(s)).strip().lower()


def _safe_float(value, default: float = 0.0) -> float:
    try:
        if value is None or value == "":
            return default
        if isinstance(value, str):
            value = value.strip().replace("%", "")
        out = float(value)
        return default if out != out else out
    except (TypeError, ValueError):
        return default


def _as_list(value) -> list:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, (tuple, set)):
        return list(value)
    return [value]


def format_elapsed(seconds: float) -> str:
    seconds = max(0, int(round(seconds)))
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


_QUOTE_MAP = str.maketrans({
    "‘": "'", "’": "'", "‚": "'", "‛": "'",
    "“": '"', "”": '"', "„": '"', "‟": '"',
    "–": "-", "—": "-", "−": "-", "‐": "-", "‑": "-",
    " ": " ", " ": " ", " ": " ", " ": " ",
})


# Adobe Symbol font encoding: PDF text extracted from the Symbol face arrives as Private Use Area code
# points U+F0xx whose low byte is the Symbol-font character code (Adobe Symbol Encoding table).
_SYMBOL_PUA = {
    0x41: "Α", 0x42: "Β", 0x43: "Χ", 0x44: "Δ", 0x45: "Ε", 0x46: "Φ", 0x47: "Γ", 0x48: "Η", 0x49: "Ι", 0x4A: "ϑ",
    0x4B: "Κ", 0x4C: "Λ", 0x4D: "Μ", 0x4E: "Ν", 0x4F: "Ο", 0x50: "Π", 0x51: "Θ", 0x52: "Ρ", 0x53: "Σ", 0x54: "Τ",
    0x55: "Υ", 0x56: "ς", 0x57: "Ω", 0x58: "Ξ", 0x59: "Ψ", 0x5A: "Ζ",
    0x61: "α", 0x62: "β", 0x63: "χ", 0x64: "δ", 0x65: "ε", 0x66: "φ", 0x67: "γ", 0x68: "η", 0x69: "ι", 0x6A: "φ",
    0x6B: "κ", 0x6C: "λ", 0x6D: "μ", 0x6E: "ν", 0x6F: "ο", 0x70: "π", 0x71: "θ", 0x72: "ρ", 0x73: "σ", 0x74: "τ",
    0x75: "υ", 0x76: "ϖ", 0x77: "ω", 0x78: "ξ", 0x79: "ψ", 0x7A: "ζ",
    0xB0: "°", 0xB1: "±", 0xB4: "×", 0xB8: "÷", 0xB9: "≠", 0xBA: "≡", 0xBB: "≈", 0xA3: "≤", 0xB3: "≥", 0xD6: "√",
    0xA5: "∞", 0xB5: "∝", 0xB6: "∂", 0xE5: "∑", 0xD5: "∏", 0xF2: "∫", 0xAE: "→", 0xAC: "←", 0xBD: "|", 0xBE: "—",
    0xD7: "·", 0x2D: "−", 0x2B: "+", 0x3D: "=", 0x28: "(", 0x29: ")",
}


def _map_symbol_pua(value: str) -> str:
    if not any(0xF000 <= ord(ch) <= 0xF0FF for ch in value):
        return value
    out = []
    for ch in value:
        code = ord(ch)
        if 0xF000 <= code <= 0xF0FF:
            out.append(_SYMBOL_PUA.get(code - 0xF000, ch))
        else:
            out.append(ch)
    return "".join(out)


def norm_cmp(s: str) -> str:
    """Comparison form: Symbol-font PUA -> Greek, NFKC, unified quotes/dashes/spaces, casefold, single spaces."""
    value = unicodedata.normalize("NFKC", _map_symbol_pua(str(s or ""))).translate(_QUOTE_MAP)
    value = value.replace("­", "")
    value = re.sub(r"\s+", " ", value).strip().casefold()
    return value


TOKEN_RE = re.compile(r"[0-9]+(?:[.,][0-9]+)*|[^\W_]+|[^\w\s]", re.UNICODE)


def tokens(s: str) -> list[str]:
    return TOKEN_RE.findall(norm_cmp(s))


def word_tokens(s: str) -> list[str]:
    return [t for t in tokens(s) if re.match(r"[^\W_]", t)]


def document_metadata(doc, path: Path) -> dict:
    first = "\n".join(doc[p].get_text("text") for p in range(min(4, doc.page_count)))
    m_std = re.search(r"\bIEC\s+(\d{3,6}(?:-\d+)*)\b", first, re.I)
    m_ed = re.search(r"\bEdition\s+(\d+(?:\.\d+)?)\b", first, re.I)
    years = re.findall(r"\b(?:19|20)\d{2}\b", first)
    return {
        "filename": path.name,
        "path": str(path.resolve()),
        "standard_number": m_std.group(1) if m_std else None,
        "edition": m_ed.group(1) if m_ed else None,
        "year": years[0] if years else None,
        "pages": doc.page_count,
    }


# ============================================================

# ============================================================

class OllamaTransportError(RuntimeError):
    """Connection-level failure (server closed the connection, reset, timeout) as opposed to a model answer."""


def _http_json(url: str, payload: dict, timeout: int = 1800) -> dict:
    import http.client
    import socket
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as e:
        try:
            detail = e.read().decode("utf-8", errors="replace").strip()
        except Exception:
            detail = ""
        msg = f"Ollama 요청 실패: HTTP {e.code} {e.reason}"
        if detail:
            msg += f"\nOllama 응답 본문: {detail[:2000]}"
        raise RuntimeError(msg) from e
    except (urllib.error.URLError, http.client.RemoteDisconnected, http.client.IncompleteRead,
            ConnectionResetError, ConnectionAbortedError, socket.timeout, TimeoutError) as e:
        raise OllamaTransportError(f"Ollama 연결 오류: {type(e).__name__}: {e}") from e
    try:
        return json.loads(raw)
    except Exception as e:
        raise RuntimeError(f"Ollama 응답 JSON 해석 실패: {raw[:800]}") from e


TRANSPORT_RETRY_WAITS = (8, 25, 60)   # seconds; covers a model reload or a server restart


def _http_json_retrying(url: str, payload: dict, timeout: int, call_id: int, log_context) -> dict:
    """Transport-level retries with increasing waits. The server occasionally drops a connection while it
    (re)loads the model or restarts; the model answer itself is never retried."""
    last: Optional[Exception] = None
    for attempt, wait in enumerate((0,) + TRANSPORT_RETRY_WAITS):
        if wait:
            time.sleep(wait)
        try:
            return _http_json(url, payload, timeout=timeout)
        except OllamaTransportError as e:
            last = e
            _log_event("LLM_TRANSPORT_RETRY", call_id=call_id, context=log_context or {}, attempt=attempt + 1,
                       next_wait_seconds=(TRANSPORT_RETRY_WAITS[attempt] if attempt < len(TRANSPORT_RETRY_WAITS) else None),
                       error=str(e)[:300])
    raise OllamaTransportError(
        f"{last} - Ollama 서버에 {len(TRANSPORT_RETRY_WAITS) + 1}회 연결을 시도했지만 실패했습니다. "
        "Ollama 앱이 실행 중인지 확인하세요."
    )


def _http_json_with_think_fallback(base_url: str, payload: dict, timeout: int, call_id: int, log_context) -> dict:
    url = base_url.rstrip("/") + "/api/chat"
    try:
        return _http_json_retrying(url, payload, timeout, call_id, log_context)
    except OllamaTransportError:
        raise
    except RuntimeError as e:
        msg = str(e)
        if "think" in payload and "HTTP 400" in msg and "think" in msg.lower():
            _log_event("LLM_THINK_FIELD_UNSUPPORTED", call_id=call_id, context=log_context or {}, error=msg[:300])
            return _http_json_retrying(url, {k: v for k, v in payload.items() if k != "think"}, timeout, call_id, log_context)
        raise


def ollama_list_models(base_url: str) -> list[str]:
    url = base_url.rstrip("/") + "/api/tags"
    try:
        with urllib.request.urlopen(url, timeout=10) as resp:
            obj = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        raise RuntimeError(f"Ollama 연결 실패: {e}") from e
    return [str(x.get("name", "")) for x in obj.get("models", []) if x.get("name")]


def ollama_chat_json(base_url: str, model: str, system: str, user: str, schema: dict, *,
                     think: bool = False, num_ctx: int = DEFAULT_NUM_CTX, num_predict: int = DEFAULT_NUM_PREDICT,
                     timeout: int = 1800, log_context: Optional[dict] = None) -> dict:
    global _LAST_TEXT_RESPONSE_META
    call_id = _next_llm_call_id()
    started = time.perf_counter()
    _log_event("LLM_CALL_START", call_id=call_id, call_type="text_json", model=model, context=log_context or {},
               num_ctx=num_ctx, num_predict=num_predict, system_chars=len(system), user_chars=len(user))
    try:
        payload = {
            "model": model,
            "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}],
            "stream": False, "format": schema, "keep_alive": "10m",
            "options": {"temperature": 0, "num_ctx": num_ctx, "num_predict": num_predict},
            "think": bool(think),
        }
        obj = _http_json_with_think_fallback(base_url, payload, timeout, call_id, log_context)
        message = obj.get("message") or {}
        content = (message.get("content") or "").strip()
        meta = {
            "done_reason": obj.get("done_reason"), "prompt_eval_count": obj.get("prompt_eval_count"),
            "eval_count": obj.get("eval_count"), "total_duration_ns": obj.get("total_duration"),
            "response_chars": len(content), "num_predict": num_predict, "num_ctx": num_ctx,
        }
        _log_event("LLM_RESPONSE_META", call_id=call_id, context=log_context or {}, **meta)
        _LAST_TEXT_RESPONSE_META = {**meta, "call_id": call_id, "prompt_chars": len(system) + len(user)}
        pec = obj.get("prompt_eval_count")
        prompt_chars = len(system) + len(user)
        if isinstance(pec, int) and pec > 1000:
            near_full = pec >= num_ctx - 256
            truncated = (prompt_chars / pec) > 6.0 and prompt_chars > num_ctx * 2.5
            if near_full or truncated:
                _log_event("LLM_CONTEXT_OVERFLOW", call_id=call_id, context=log_context or {},
                           prompt_eval_count=pec, num_ctx=num_ctx, prompt_chars=prompt_chars)
                raise RuntimeError(
                    "입력 프롬프트가 컨텍스트 한도를 넘었거나 Ollama가 프롬프트를 잘라낸 것으로 보입니다. "
                    f"prompt_eval_count={pec}, num_ctx={num_ctx}, prompt_chars={prompt_chars}."
                )
        if not content:
            raise RuntimeError(f"Ollama가 빈 응답을 반환했습니다. done_reason={obj.get('done_reason')!r}")
        try:
            parsed = json.loads(content)
        except Exception as e:
            _log_event("LLM_JSON_PARSE_ERROR", call_id=call_id, context=log_context or {}, **meta,
                       response_head=content[:1200], response_tail=content[-500:], json_error=str(e))
            if obj.get("done_reason") == "length":
                detail = (f"모델 응답이 길이 제한으로 종료됐습니다. prompt_eval_count={pec!r}, num_ctx={num_ctx}, "
                          f"eval_count={obj.get('eval_count')!r}, num_predict={num_predict}.")
            else:
                detail = f"모델이 완결되지 않은 JSON을 반환했습니다. done_reason={obj.get('done_reason')!r}."
            raise RuntimeError(f"{detail} JSON 오류={e}; 응답 시작={content[:500]!r}") from e
        if not isinstance(parsed, dict):
            raise RuntimeError(f"모델이 JSON 객체가 아닌 값을 반환했습니다: type={type(parsed).__name__}")
        _log_event("LLM_CALL_END", call_id=call_id, context=log_context or {},
                   elapsed_seconds=round(time.perf_counter() - started, 3), response_chars=len(content))
        return parsed
    except Exception as e:
        _log_event("LLM_CALL_ERROR", call_id=call_id, context=log_context or {},
                   elapsed_seconds=round(time.perf_counter() - started, 3), error_type=type(e).__name__, error=str(e))
        raise


def ollama_vision_json(base_url: str, model: str, system: str, user: str, images_b64: list[str], schema: dict, *,
                       num_ctx: int = DEFAULT_NUM_CTX, timeout: int = 1800, log_context: Optional[dict] = None) -> dict:
    call_id = _next_llm_call_id()
    started = time.perf_counter()
    _log_event("LLM_CALL_START", call_id=call_id, call_type="vision_json", model=model, context=log_context or {},
               image_count=len(images_b64))
    try:
        payload = {
            "model": model,
            "messages": [{"role": "system", "content": system}, {"role": "user", "content": user, "images": images_b64}],
            "stream": False, "format": schema, "keep_alive": "10m",
            "options": {"temperature": 0, "num_ctx": num_ctx, "num_predict": DEFAULT_VISION_NUM_PREDICT},
            "think": False,
        }
        obj = _http_json_with_think_fallback(base_url, payload, timeout, call_id, log_context)
        content = ((obj.get("message") or {}).get("content") or "").strip()
        if not content:
            raise RuntimeError(f"VLM이 빈 응답을 반환했습니다. done_reason={obj.get('done_reason')!r}")
        parsed = json.loads(content)
        if not isinstance(parsed, dict):
            raise RuntimeError("VLM이 JSON 객체가 아닌 값을 반환했습니다.")
        _log_event("LLM_CALL_END", call_id=call_id, call_type="vision_json", context=log_context or {},
                   elapsed_seconds=round(time.perf_counter() - started, 3))
        return parsed
    except Exception as e:
        _log_event("LLM_CALL_ERROR", call_id=call_id, call_type="vision_json", context=log_context or {},
                   error_type=type(e).__name__, error=str(e))
        raise


# ============================================================
# Stage 1 - PDF lines with typography and geometry
# ============================================================

@dataclass
class Line:
    side: str
    page: int
    block_no: int
    line_no: int
    text: str
    bbox: tuple
    size: float
    bold: bool
    y_ratio: float          # vertical centre / page height
    page_height: float
    removed: Optional[str] = None   # None | 'header_footer' | 'page_number' | 'toc' | 'language'
    italic: bool = False    # dominant span in italic type (ISO 80000-1: quantity symbols are set in italics)
    words: list = field(default_factory=list)   # (x0, y0, x1, y1, text) of the line's words, for word-level boxes
    in_graphic: bool = False                    # the line sits inside a vector drawing / image of the page (figure, formula)

    @property
    def block_id(self) -> str:
        return f"{self.side}-P{self.page:03d}-B{self.block_no:03d}"

    @property
    def line_id(self) -> str:
        return f"{self.block_id}-L{self.line_no:02d}"


def extract_lines(doc, side: str) -> list[Line]:
    """All text lines of the document with font size / bold flag and geometry (reading order)."""
    out: list[Line] = []
    for page_no in range(1, doc.page_count + 1):
        page = doc[page_no - 1]
        height = float(page.rect.height) or 1.0
        try:
            data = page.get_text("dict", sort=True)
        except TypeError:
            data = page.get_text("dict")
        bno = 0
        first_idx = len(out)
        for block in data.get("blocks", []):
            if block.get("type", 0) != 0:
                continue
            bno += 1
            lno = 0
            for line in block.get("lines", []):
                spans = [sp for sp in line.get("spans", []) if str(sp.get("text", "")).strip()]
                if not spans:
                    continue
                text = clean(_map_symbol_pua("".join(str(sp.get("text", "")) for sp in line.get("spans", []))))
                if not text:
                    continue
                lno += 1
                # Size and weight of the dominant span (by non-blank character count; ties -> first span).
                dom = max(spans, key=lambda sp: len(str(sp.get("text", "")).strip()))
                size = float(dom.get("size", 0.0) or 0.0)
                flags = int(dom.get("flags", 0) or 0)
                font = str(dom.get("font", ""))
                bold = bool(flags & 16) or ("bold" in font.lower()) or ("black" in font.lower() and "bold" not in font.lower())
                italic = bool(flags & 2) or ("italic" in font.lower()) or ("oblique" in font.lower())
                bbox = tuple(float(x) for x in (line.get("bbox") or block.get("bbox")))
                out.append(Line(side=side, page=page_no, block_no=bno, line_no=lno, text=text, bbox=bbox,
                                size=size, bold=bold, y_ratio=((bbox[1] + bbox[3]) / 2.0) / height,
                                page_height=height, italic=italic))
        try:
            _attach_words(out[first_idx:], page.get_text("words"))
        except Exception:
            pass
        try:
            graphics = _graphics_of_page(page)
            for ln in out[first_idx:]:
                c = fitz.Point((ln.bbox[0] + ln.bbox[2]) / 2.0, (ln.bbox[1] + ln.bbox[3]) / 2.0)
                ln.in_graphic = any(g.contains(c) for g in graphics)
        except Exception:
            pass
    return out


def _graphics_of_page(page) -> list:
    """Vector-drawing clusters and raster images of a page, read from the document itself (PyMuPDF
    cluster_drawings and image blocks). A cluster that contains every text line of the page is the page frame or
    a full-page box, not a figure, and is left out. Used to tag formula / figure text (Line.in_graphic) and to
    widen fragment boxes to the drawing they sit in."""
    rects = []
    try:
        rects += [fitz.Rect(r) for r in page.cluster_drawings()]
    except Exception:
        pass
    text_union = None
    try:
        d = page.get_text("dict")
        rects += [fitz.Rect(b["bbox"]) for b in d.get("blocks", []) if b.get("type") == 1]
        for b in d.get("blocks", []):
            if b.get("type") != 0:
                continue
            for l in b.get("lines", []):
                if any(str(sp.get("text", "")).strip() for sp in l.get("spans", [])):
                    r = fitz.Rect(l["bbox"])
                    text_union = r if text_union is None else text_union | r
    except Exception:
        pass
    return [r for r in rects if not r.is_empty and not (text_union is not None and r.contains(text_union))]


def _attach_words(lines: list, words: list) -> None:
    """Give every line the words PyMuPDF extracted inside it (word = whitespace-delimited string with its box).
    Matching is by geometry - the word's centre inside the line box - because the 'dict' and 'words' extractions
    number blocks differently. The word boxes let a difference be shown at its exact place in the line."""
    if not lines or not words:
        return
    for w in words:
        try:
            x0, y0, x1, y1 = (float(v) for v in w[:4])
            text = _map_symbol_pua(str(w[4]))
        except Exception:
            continue
        if not text.strip():
            continue
        cx, cy = (x0 + x1) / 2.0, (y0 + y1) / 2.0
        for ln in lines:
            b = ln.bbox
            if b[1] - 1.0 <= cy <= b[3] + 1.0 and b[0] - 2.0 <= cx <= b[2] + 2.0:
                ln.words.append((x0, y0, x1, y1, text))
                break


# ============================================================
# Stage 2 - Normalisation: headers/footers, TOC, language, de-hyphenation
# ============================================================

_PAGE_NUMBER_RE = re.compile(r"^[\s–—\-–—]*\d{1,4}[\s–—\-–—]*$")
_TOC_LINE_RE = re.compile(r"(?:\.\s*){3,}\s*\d{1,4}\s*$|\s\d{1,4}\s*$")


def _hf_signature(text: str) -> str:
    value = norm_cmp(text)
    value = re.sub(r"\d+", "#", value)
    value = re.sub(r"[^\w#]+", " ", value).strip()
    return value


def mark_running_headers_footers(lines: list[Line], page_count: int) -> dict:
    """Repetition-based header/footer detection.

    A line in the top/bottom band whose digit-masked text recurs on >= 25 % of pages (>= 3) is a
    running header/footer; bare page numbers in the bands are removed too. This is the
    "same text at the same position on many pages" criterion of Lin (HP Labs 2002) and
    Dejean & Meunier (2006); we use document-wide repetition instead of neighbour pairs so that
    alternating odd/even headers are handled.
    """
    band = HEADER_FOOTER_BAND_RATIO
    body_size = body_font_size(lines)
    # The signature carries typography as well as text: running headers repeat in the same face
    # and size, whereas a bold clause number that happens to sit at the top of a page does not.
    def signature(ln: Line) -> tuple:
        zone = "top" if ln.y_ratio <= band else "bottom"
        return (zone, _hf_signature(ln.text), round(ln.size), bool(ln.bold))

    sig_pages: dict[tuple, set] = defaultdict(set)
    for ln in lines:
        if ln.y_ratio <= band or ln.y_ratio >= 1.0 - band:
            sig_pages[signature(ln)].add(ln.page)
    min_pages = max(3, math.ceil(page_count * HEADER_FOOTER_MIN_PAGE_RATIO))
    repeated = {k for k, pages in sig_pages.items() if len(pages) >= min_pages and k[1]}
    removed_hf = removed_pn = 0
    for ln in lines:
        if ln.removed:
            continue
        in_band = ln.y_ratio <= band or ln.y_ratio >= 1.0 - band
        if not in_band:
            continue
        typographic = ln.bold or ln.size >= body_size + 0.8
        if signature(ln) in repeated:
            ln.removed = "header_footer"
            removed_hf += 1
        elif _PAGE_NUMBER_RE.match(ln.text) and not typographic:
            ln.removed = "page_number"
            removed_pn += 1
    stats = {"header_footer_signatures": len(repeated), "header_footer_lines": removed_hf,
             "page_number_lines": removed_pn, "min_pages_for_signature": min_pages,
             "signatures": sorted({f"{k[1]} ({k[2]}pt{' bold' if k[3] else ''})" for k in repeated})[:12]}
    _log_event("NORMALISE_HEADERS", side=lines[0].side if lines else "?", **stats)
    return stats


def mark_toc_pages(lines: list[Line]) -> dict:
    """Pages dominated by 'title .... 12' lines are a table of contents (excluded from the body).

    Lines already removed as bare page numbers are reconsidered here: on a TOC page a bare number in the page
    band is an entry number ("8" above "Short-time direct current ..... 47"); the page's own number carries the
    repeated header/footer signature and stays removed."""
    by_page: dict[int, list[Line]] = defaultdict(list)
    for ln in lines:
        if ln.removed in (None, "page_number"):
            by_page[ln.page].append(ln)
    toc_pages = []
    toc_entries = []
    leader_re = re.compile(r"(?:\.\s*){3,}")
    num_re = re.compile(r"^((?:\d+(?:\.\d+)*)|[A-Z](?:\.\d+)+|Annex\s+[A-Z]|Bibliography|Index)\b\s*(.*)$", re.I)
    for page, rows_all in sorted(by_page.items()):
        rows = []
        for k, r in enumerate(rows_all):
            if r.removed == "page_number":
                # reconsidered only in the TOC pattern "number line" + "title ..... page" line; otherwise it stays a page number
                nxt = rows_all[k + 1] if k + 1 < len(rows_all) else None
                if nxt is None or not leader_re.search(nxt.text) or num_re.match(nxt.text.strip()):
                    continue
            rows.append(r)
        if len(rows) < 6:
            continue
        leader = sum(1 for r in rows if leader_re.search(r.text))
        if leader / len(rows) >= TOC_LINE_RATIO:
            toc_pages.append(page)
            # Entries may be split over lines: "5.7" / "Ambient temperature effect ....... 23" / "23".
            pending_number = None
            pending_title = ""
            for r in rows:
                r.removed = "toc"
                text = r.text.strip()
                m = num_re.match(text)
                if m and not m.group(2).strip():
                    pending_number, pending_title = m.group(1), ""
                    continue
                number = m.group(1) if m else pending_number
                title_part = m.group(2) if m else text
                if number is None:
                    continue
                if not leader_re.search(title_part):
                    # Wrapped entry: the first title line(s) carry no dot leader; keep them for the last line.
                    pending_number = number
                    if len(pending_title) < 200:
                        pending_title = (pending_title + " " + title_part).strip()
                    continue
                title = clean((pending_title + " " + leader_re.split(title_part)[0]).strip())
                m_pg = re.search(r"(\d{1,4})\s*$", title_part)
                toc_entries.append({"number": number, "title": title, "page": int(m_pg.group(1)) if m_pg else None})
                pending_number, pending_title = None, ""
    stats = {"toc_pages": toc_pages, "toc_entries": len(toc_entries)}
    _log_event("NORMALISE_TOC", side=lines[0].side if lines else "?", **stats)
    return {"pages": toc_pages, "entries": toc_entries}


_LANG_SHARED = EN_STOPWORDS & FR_STOPWORDS          # "me", "on": evidence for neither language
_LANG_EN = frozenset(w for w in EN_STOPWORDS if len(w) >= 2 and w not in _LANG_SHARED)
_LANG_FR = frozenset(w for w in FR_STOPWORDS if len(w) >= 2 and w not in _LANG_SHARED)


def _binomial_sign_p(k: int, n: int) -> float:
    """One-sided sign test: P(X >= k) for X ~ Binomial(n, 1/2)."""
    if n <= 0 or k <= 0:
        return 1.0
    if n > 1000:                                       # normal approximation with continuity correction
        z = (k - 0.5 - n / 2.0) / math.sqrt(n / 4.0)
        return 0.5 * math.erfc(z / math.sqrt(2.0))
    return sum(math.comb(n, i) for i in range(k, n + 1)) / float(2 ** n)


def mark_non_english_pages(lines: list[Line]) -> dict:
    """Common-short-word language identification per page (Grefenstette 1995) with the Snowball word lists.

    IEC publications are often bilingual (English followed by French). For every page the English and the French
    stop-word hits are counted; the page is excluded when the French hits outnumber the English ones
    *significantly* under the one-sided binomial sign test (p < 0.05): one or two French words on a cover or a
    figure page are not evidence, a page of French prose is. No minimum token count and no minimum hit count are
    needed. Every exclusion is logged with its counts.
    """
    by_page: dict[int, list[str]] = defaultdict(list)
    elisions: Counter = Counter()
    for ln in lines:
        if not ln.removed:
            by_page[ln.page].extend(word_tokens(ln.text))
            elisions[ln.page] += len(FR_ELISION_RE.findall(norm_cmp(ln.text)))
    excluded, detail = [], {}
    for page, toks in by_page.items():
        en = sum(1 for t in toks if t in _LANG_EN)
        fr = sum(1 for t in toks if t in _LANG_FR) + elisions[page]
        if fr > en and _binomial_sign_p(fr, en + fr) < 0.05:
            excluded.append(page)
            detail[page] = {"en": en, "fr": fr}
    excluded_set = set(excluded)
    for ln in lines:
        if not ln.removed and ln.page in excluded_set:
            ln.removed = "language"
    stats = {"non_english_pages": len(excluded), "first_excluded_pages": sorted(excluded)[:10],
             "excluded_page_counts": {str(k): detail[k] for k in sorted(detail)[:10]}}
    _log_event("NORMALISE_LANGUAGE", side=lines[0].side if lines else "?", **stats)
    return stats


def build_lexicon(all_lines: list[list[Line]]) -> set[str]:
    """Document-internal lexicon used to decide whether a line-end hyphen is a soft break."""
    lex: set[str] = set()
    for lines in all_lines:
        for ln in lines:
            for t in word_tokens(ln.text):
                if len(t) >= 3 and not t.isdigit():
                    lex.add(t)
    return lex


def join_hyphenated(prev: str, nxt: str, lexicon: set[str]) -> tuple[str, bool]:
    """Join 'measur-' + 'ing' into 'measuring' only when the joined word is attested in the corpus.

    Conservative rule from the PDF-extraction literature (Bast & Korzen 2017 and the Freiburg
    de-hyphenation work): compounds such as 'high-quality' keep their hyphen when the hyphen-free
    form is not a known word.
    """
    m = re.search(r"(\S+)-$", prev)
    if not m:
        return prev + " " + nxt, False
    first = m.group(1)
    m2 = re.match(r"^([a-zA-Z]+)(.*)$", nxt)
    if not m2:
        return prev + " " + nxt, False
    second, rest = m2.group(1), m2.group(2)
    joined = (first + second)
    if joined.casefold() in lexicon and second[:1].islower():
        return prev[: -len(first) - 1] + joined + rest, True
    return prev + nxt if second[:1].islower() else prev + " " + nxt, False


# ============================================================
# Stage 3 - Logical structure (ISO/IEC Directives Part 2 numbering, ISO 10241-1 entries)
# ============================================================

CLAUSE_NUM_RE = re.compile(r"^(\d{1,2}(?:\.\d{1,3}){0,6})(?:\s+|$)")
ANNEX_NUM_RE = re.compile(r"^([A-Z](?:\.\d{1,3}){1,6})(?:\s+|$)")
ANNEX_HEAD_RE = re.compile(r"^Annex\s+([A-Z])\b\s*(.*)$", re.I)
TERMINAL_HEAD_RE = re.compile(r"^(Bibliography|Index)\s*$", re.I)
NOTE_RE = re.compile(r"^(?:NOTE|Note)\s*(\d*)(?:\s+to\s+entry)?\s*[:\-–—]?\s*(.*)$")
SOURCE_RE = re.compile(r"^\[(?:SOURCE\s*:\s*)?(?:IEC|ISO|CISPR|IEEE|ITU|EN)\b[^\]]*\]?", re.I)
SOURCE_ANY_RE = re.compile(r"^\[(?:SOURCE\s*:)?[^\]]{3,}\]?$", re.I)
CAPTION_RE = re.compile(r"^(Figure|Table)\s+([A-Z]?\.?\d+[a-z]?)\s*[–\-—]\s*(.+)$")
LIST_ITEM_RE = re.compile(r"^([a-z]\)|\d+\)|[–•\-])\s+")
LONE_MARKER_RE = re.compile(r"^[–•]$")     # bullet / dash alone on its line; the item text follows on the same baseline
EQUATION_NO_RE = re.compile(r"\((\d{1,3})\)\s*$")
TERMS_CLAUSE_TITLE_RE = re.compile(r"\b(terms?\s+and\s+definitions|definitions|terminology)\b", re.I)


@dataclass
class Paragraph:
    kind: str                      # body | term | definition | note | source | caption | list | equation | heading_text
    text: str
    lines: list[Line]
    label: str = ""                # note number, caption number, list marker

    @property
    def side(self) -> str:
        return self.lines[0].side if self.lines else "?"

    def pages(self) -> list[int]:
        return sorted({ln.page for ln in self.lines})

    def anchors(self) -> list[dict]:
        """Per-page union bbox of the paragraph's lines, for highlighting."""
        out = []
        for page in self.pages():
            boxes = [ln.bbox for ln in self.lines if ln.page == page]
            out.append({"page": page, "bbox": [min(b[0] for b in boxes), min(b[1] for b in boxes),
                                                max(b[2] for b in boxes), max(b[3] for b in boxes)],
                        "line_ids": [ln.line_id for ln in self.lines if ln.page == page]})
        return out


@dataclass
class Section:
    side: str
    number: str                    # "3.6.7", "A.2", "Annex B", "Bibliography"
    title: str
    level: int
    kind: str                      # clause | entry | annex | terminal
    heading_lines: list[Line] = field(default_factory=list)
    paragraphs: list[Paragraph] = field(default_factory=list)
    term: str = ""                 # terminological entry: preferred term
    symbol: str = ""
    children: list = field(default_factory=list)
    parent: Optional["Section"] = None
    tables: list = field(default_factory=list)   # TableBlock objects located in this section

    @property
    def sid(self) -> str:
        return f"{self.side}:{self.number}"

    def page_range(self) -> tuple[int, int]:
        pages = [ln.page for ln in self.heading_lines] + [ln.page for p in self.paragraphs for ln in p.lines]
        return (min(pages), max(pages)) if pages else (0, 0)

    def body_text(self) -> str:
        return "\n".join(p.text for p in self.paragraphs)

    def path(self) -> str:
        parts = []
        node = self
        while node is not None:
            parts.append(node.number)
            node = node.parent
        return " > ".join(reversed(parts))


@dataclass
class TableBlock:
    """A ruled table recognised by PyMuPDF's table finder, kept as a cell grid with cell geometry."""
    side: str
    page: int
    bbox: tuple
    cells: list                 # rows -> list of cell text ('' when empty)
    cell_boxes: list            # rows -> list of (x0, y0, x1, y1) or None
    label: str = ""             # "table 3" (lower-case caption label) when a caption is found nearby
    section: Optional["Section"] = None

    @property
    def shape(self) -> tuple:
        return (len(self.cells), max((len(r) for r in self.cells), default=0))

    def flat_text(self) -> str:
        return "\n".join(" | ".join(c for c in row) for row in self.cells)

    def anchors(self) -> list[dict]:
        return [{"page": self.page, "bbox": [float(x) for x in self.bbox]}]


def extract_tables(doc, side: str) -> list[TableBlock]:
    """Ruled tables via PyMuPDF find_tables (line strategy). Text inside a table is compared cell by cell
    later instead of being treated as prose; this is where PDF text extraction is least reliable."""
    out: list[TableBlock] = []
    if not hasattr(doc[0], "find_tables"):
        _log_event("TABLE_FINDER_UNAVAILABLE", side=side)
        return out
    for page_no in range(1, doc.page_count + 1):
        page = doc[page_no - 1]
        try:
            finder = page.find_tables()
        except Exception as e:
            _log_event("TABLE_FINDER_ERROR", side=side, page=page_no, error=str(e)[:200])
            continue
        for t in getattr(finder, "tables", []):
            try:
                data = t.extract()
            except Exception:
                continue
            rows = [[clean(_map_symbol_pua(str(c))) if c is not None else "" for c in row] for row in data]
            if len(rows) < 2 or max((len(r) for r in rows), default=0) < 2:
                continue
            if sum(1 for r in rows for c in r if c) < 2:
                continue
            boxes = []
            for r in getattr(t, "rows", []):
                boxes.append([tuple(float(x) for x in c) if c is not None else None for c in r.cells])
            out.append(TableBlock(side=side, page=page_no, bbox=tuple(float(x) for x in t.bbox), cells=rows, cell_boxes=boxes))
    _log_event("TABLES_EXTRACTED", side=side, tables=len(out), pages_with_tables=len({t.page for t in out}))
    return out


def mark_table_lines(lines: list[Line], tables: list[TableBlock]) -> int:
    by_page: dict[int, list[TableBlock]] = defaultdict(list)
    for t in tables:
        by_page[t.page].append(t)
    n = 0
    for ln in lines:
        if ln.removed:
            continue
        cx, cy = (ln.bbox[0] + ln.bbox[2]) / 2.0, (ln.bbox[1] + ln.bbox[3]) / 2.0
        for t in by_page.get(ln.page, []):
            x0, y0, x1, y1 = t.bbox
            if x0 - 1 <= cx <= x1 + 1 and y0 - 1 <= cy <= y1 + 1:
                ln.removed = "table"
                n += 1
                break
    return n


def attach_tables(sections: list[Section], tables: list[TableBlock]) -> None:
    """Each table belongs to the section whose heading is the last one before it in reading order; the
    nearest 'Table n' caption paragraph on the same page gives its label."""
    heads = []
    for s in sections:
        if s.heading_lines:
            h = s.heading_lines[0]
            heads.append((h.page, h.bbox[1], s))
    heads.sort(key=lambda x: (x[0], x[1]))
    for t in tables:
        owner = None
        for page, y, s in heads:
            if (page, y) <= (t.page, t.bbox[1]):
                owner = s
            else:
                break
        if owner is None:
            continue
        t.section = owner
        owner.tables.append(t)
        best, best_d = "", 1e9
        for p in owner.paragraphs:
            if p.kind != "caption" or not p.lines or p.lines[0].page != t.page:
                continue
            m = _CAPTION_LABEL_RE.match(p.text)
            if not m or m.group(1).lower() != "table":
                continue
            d = abs(p.lines[0].bbox[1] - t.bbox[1])
            if d < best_d:
                best, best_d = f"{m.group(1).lower()} {m.group(2).lower()}", d
        t.label = best


def _number_parts(number: str) -> list:
    """'3.6.7' -> [3, 6, 7]; 'A.2' -> ['A', 2]; 'Annex B' -> ['B']."""
    m = ANNEX_HEAD_RE.match(number)
    if m:
        return [m.group(1).upper()]
    parts = []
    for p in number.split("."):
        parts.append(int(p) if p.isdigit() else p.upper())
    return parts


def _is_valid_successor(parts: list, open_numbers: list[list], number: str = "", toc_numbers: frozenset = frozenset(),
                        typographic: bool = True) -> bool:
    """Sequential-numbering check from ISO/IEC Directives Part 2 (clauses and annexes are numbered consecutively;
    Clause 1 is the Scope): a heading number is accepted when it continues the hierarchy - next sibling of an open
    level, first child of the current node, or the next top-level clause / annex letter. This rejects body-text
    fragments like '3.2 kV'.

    The chain starts at Clause 1 (or Annex A). Any other start, and any gap in a sibling sequence, is accepted only
    on evidence from the document itself: the number is listed in its table of contents, or - when the TOC does not
    enumerate that level at all - the line is set in heading type. There is no hand-chosen tolerance.
    """
    listed = number in toc_numbers

    def gap_ok() -> bool:
        if listed:
            return True
        depth, prefix = len(parts), parts[:-1]
        toc_covers_level = any(len(q) == depth and q[:-1] == prefix for q in map(_number_parts, toc_numbers))
        return typographic and not toc_covers_level

    if not open_numbers:
        if len(parts) == 1 and isinstance(parts[0], int):
            return parts[0] == 1 or listed
        return len(parts) == 1 and isinstance(parts[0], str) and (parts[0] == "A" or listed)
    for depth in range(len(open_numbers), 0, -1):
        prev = open_numbers[depth - 1]
        # first child of the deepest open node
        if depth == len(open_numbers) and len(parts) == len(prev) + 1 and parts[:-1] == prev and parts[-1] == 1:
            return True
        # next sibling at this depth; a skipped number (a heading the extractor or the authors skipped) needs evidence
        if len(parts) == len(prev) and parts[:-1] == prev[:-1]:
            a, b = prev[-1], parts[-1]
            if isinstance(a, int) and isinstance(b, int):
                step = b - a
            elif isinstance(a, str) and isinstance(b, str) and len(a) == 1 and len(b) == 1:
                step = ord(b) - ord(a)
            else:
                continue
            if step == 1 or (step > 1 and gap_ok()):
                return True
    # new annex letter after numeric clauses, or first annex 'A'
    if len(parts) == 1 and isinstance(parts[0], str):
        letters = [o[0] for o in open_numbers if isinstance(o[0], str)]
        if not letters:
            return parts[0] == "A" or listed
        step = ord(parts[0]) - ord(letters[-1])
        return step == 1 or (step > 1 and gap_ok())
    return False


def body_font_size(lines: list[Line]) -> float:
    """Dominant font size by character count = body text size (Klampfl et al. 2014 use font
    statistics to separate headings from body)."""
    counter: Counter = Counter()
    for ln in lines:
        if not ln.removed and ln.size > 0:
            counter[round(ln.size, 1)] += len(ln.text)
    return counter.most_common(1)[0][0] if counter else 10.0


def _norm_title(text: str) -> str:
    t = re.sub(r"\((?:normative|informative)\)", " ", text or "", flags=re.I)
    t = re.sub(r"(?:\.\s*){3,}.*$", " ", t)           # dot leader and page number
    t = re.sub(r"\s\d{1,4}\s*$", " ", t)               # trailing page number
    t = re.sub(r"[^0-9a-zA-Z\u00C0-\u024F\u0370-\u03FF]+", " ", t.lower())
    return re.sub(r"\s+", " ", t).strip()


def _toc_title_match(text: str, toc_title: str) -> bool:
    """Heading text vs. the TOC entry's title: equal, one a prefix of the other (wrapped lines), the TOC
    fragment contained in the heading, or close under Ratcliff/Obershelp (>= 0.8)."""
    a, b = _norm_title(text), _norm_title(toc_title)
    if len(a) < 3 or len(b) < 3:
        return False
    if a == b or a.startswith(b) or b.startswith(a) or (len(b) >= 6 and b in a):
        return True
    return difflib.SequenceMatcher(None, a, b).ratio() >= 0.8


def _heading_candidate(ln: Line, body_size: float, toc_map: Optional[dict] = None, next_text: str = "") -> Optional[tuple[str, str, str, str]]:
    """Return (kind, number, title, evidence) if the line looks like a heading under Directives numbering.

    evidence is "type" when the line is set in heading type (bold / larger than body) or "toc" when a plain-type
    line is vouched for by the document's own table of contents: the TOC lists the same number AND its title
    matches the line (or, for a bare number line, the following line) - matching TOC entries against body headings
    as in Dejean & Meunier (2005). Number alone is never enough: cross-references ("Annex A and Annex B ...") and
    figure labels ("1", "2") start with TOC numbers as well. No length limits and no stop words: what the line says
    is checked against the TOC, and whether the number fits the hierarchy is checked by _is_valid_successor.
    """
    text = ln.text.strip()
    toc_map = toc_map or {}
    evidence = "type" if (ln.bold or ln.size >= body_size + 0.8) else ""
    m = ANNEX_HEAD_RE.match(text)
    if m:
        key = f"Annex {m.group(1).upper()}"
        rest = clean(m.group(2))
        if not evidence and key in toc_map:
            status_only = not rest or bool(re.match(r"^\((?:normative|informative)\)\s*$", rest, re.I))
            if _toc_title_match(rest, toc_map[key]) or (status_only and _toc_title_match(next_text, toc_map[key])):
                evidence = "toc"
        return ("annex", key, rest, evidence) if evidence else None
    if TERMINAL_HEAD_RE.match(text):
        if not evidence and text.strip().title() in {k.title() for k in toc_map}:
            evidence = "toc"
        return ("terminal", text.strip().title(), "", evidence) if evidence else None
    m = CLAUSE_NUM_RE.match(text) or ANNEX_NUM_RE.match(text)
    if not m:
        return None
    number = m.group(1)
    rest = clean(text[m.end():])
    if rest and rest[0] in ".,;:)":
        return None                     # "3.2." / "5)" are list markers, not clause numbers (Directives numbering)
    if not evidence and number in toc_map:
        if (rest and _toc_title_match(rest, toc_map[number])) or (not rest and _toc_title_match(next_text, toc_map[number])):
            evidence = "toc"
    if not evidence:
        return None
    if not rest:
        return ("number_only", number, "", evidence)      # number alone on the line, title on the next line(s)
    return ("clause", number, rest, evidence)


def _is_status_line(text: str) -> bool:
    return bool(re.match(r"^\((?:normative|informative)\)\s*$", text.strip(), re.I))


_SYMBOL_TOKEN_RE = re.compile(r"^[A-Za-z\u0370-\u03ff][\w\u0370-\u03ff(),/'\-]*$")


def _symbol_token(text: str) -> bool:
    """A terminological entry's symbol line (ISO 10241-1 layout: term line, optional symbol line, definition):
    one token of letters / digits / parentheses, whatever its length. Definitions are phrases, never one token."""
    return bool(_SYMBOL_TOKEN_RE.match(text.strip()))


def extract_structure(lines: list[Line], side: str, lexicon: set[str], toc_entries: Optional[list] = None) -> dict:
    """Lines -> ordered list of Sections with kind-tagged Paragraphs.

    Headings: Directives numbering + typography (or presence in the document's own TOC) + sequential-numbering
    validation. Terminological entries (ISO 10241-1): number line, term line(s), optional symbol, definition,
    'Note n to entry'/'NOTE n', '[SOURCE: ...]'. Older layouts with 'n.n term' on one line are accepted.
    """
    live = [ln for ln in lines if not ln.removed]
    body_size = body_font_size(live)
    toc_map: dict = {}
    for e in toc_entries or []:
        num = str(e.get("number", "")).strip()
        m_ax = re.match(r"^Annex\s+([A-Z])$", num, re.I)
        toc_map[f"Annex {m_ax.group(1).upper()}" if m_ax else num] = str(e.get("title", ""))
    toc_numbers = frozenset(toc_map)
    via_toc = 0
    sections: list[Section] = []
    open_numbers: list[list] = []
    stack: list[Section] = []
    current: Optional[Section] = None
    front_matter: list[Line] = []
    rejected_candidates = 0
    accepted = 0
    i = 0
    n = len(live)
    terms_clause_numbers: set[str] = set()

    def push_section(sec: Section):
        nonlocal current
        parts = _number_parts(sec.number)
        while stack and len(_number_parts(stack[-1].number)) >= len(parts):
            stack.pop()
            open_numbers.pop()
        sec.parent = stack[-1] if stack else None
        if sec.parent is not None:
            sec.parent.children.append(sec)
        sec.level = len(parts)
        stack.append(sec)
        open_numbers.append(parts)
        sections.append(sec)
        current = sec

    def in_terms_clause() -> bool:
        node = current
        while node is not None:
            if node.number in terms_clause_numbers:
                return True
            node = node.parent
        return False

    def _is_marker_or_heading(l: Line) -> bool:
        return bool(_heading_candidate(l, body_size, toc_map)) or bool(_paragraph_marker(l.text)[0])

    def _heading_at(idx: int):
        l = live[idx]
        nxt = live[idx + 1].text if idx + 1 < n and live[idx + 1].page == l.page else ""
        if _is_status_line(nxt) and idx + 2 < n and live[idx + 2].page == l.page:
            nxt = nxt + " " + live[idx + 2].text          # "Annex A" / "(informative)" / title
        return _heading_candidate(l, body_size, toc_map, nxt)

    def _collect_title(start: int, first: Line, allow_plain_first: bool) -> tuple[list[Line], int]:
        """Title line(s) following a bare number / 'Annex X' heading line.

        The first title line must be on the same page and (unless allow_plain_first) set in heading
        type; wrapped continuation lines are heading-type lines in the same PDF block set exactly like the first
        title line (same weight, slant and size). A line set differently - an italic or larger single token after
        a term - is the entry's quantity symbol (ISO 80000-1: quantity symbols in italic), not title text.
        Returns (lines, next_i).
        """
        got: list[Line] = []
        k = start
        while k < n:
            l = live[k]
            if l.page != first.page or _is_marker_or_heading(l):
                break
            typo = l.bold or l.size >= body_size + 0.8
            if not got:
                if not (typo or allow_plain_first):
                    break
                got.append(l)
                k += 1
                continue
            same_face = (l.bold, l.italic, round(l.size, 1)) == (got[0].bold, got[0].italic, round(got[0].size, 1))
            # A wrapped title line keeps the title's left edge and size inside the same PDF block (MuPDF groups the
            # lines of one paragraph into one block; a body paragraph starts a new block at the margin). The weight
            # flag alone is not trusted for it: in the OLD edition the title of 5.2.1 wraps into a line whose font
            # subset reports no bold flag ("... with a reference measuring" / "system (preferred method)"), and
            # treating that line as body text produced a spurious ADD/DELETE pair.
            wrapped = (l.block_no == got[-1].block_no and abs(l.bbox[0] - got[0].bbox[0]) < 1.5
                       and round(l.size, 1) == round(got[0].size, 1) and not allow_plain_first
                       and (got[0].bold or got[0].size >= body_size + 0.8))
            if l.block_no == got[-1].block_no and ((typo and same_face) or wrapped):
                got.append(l)
                k += 1
                continue
            break
        return got, k

    while i < n:
        ln = live[i]
        cand = _heading_at(i)
        if cand is not None:
            kind, number, title, evidence = cand
            parts = _number_parts(number)
            valid = _is_valid_successor(parts, open_numbers, number, toc_numbers, evidence == "type") if kind != "terminal" else True
            if kind == "number_only":
                # Bare number line (heading type) + title/term on the following line(s):
                # the layout of ISO 10241-1 entries and of most IEC clause headings.
                if valid:
                    inside_terms = in_terms_clause()
                    plain_heading = evidence == "toc"
                    title_lines, k = _collect_title(i + 1, ln, allow_plain_first=inside_terms or plain_heading)
                    if title_lines:
                        title_text = clean(" ".join(l.text for l in title_lines))
                        is_entry = inside_terms and len(parts) >= 2
                        sec = Section(side=side, number=number, title=title_text, level=len(parts),
                                      kind="entry" if is_entry else "clause", heading_lines=[ln] + title_lines)
                        if is_entry:
                            sec.term = title_text
                        elif TERMS_CLAUSE_TITLE_RE.search(title_text) and len(parts) <= 2:
                            terms_clause_numbers.add(number)
                        push_section(sec)
                        accepted += 1
                        via_toc += int(evidence == "toc")
                        i = k
                        # optional symbol line for entries (ISO 10241-1 allows a symbol after the term)
                        if is_entry and i < n:
                            sym = live[i]
                            if sym.page == ln.page and not _is_marker_or_heading(sym) and _symbol_token(sym.text):
                                sec.symbol = sym.text
                                sec.heading_lines.append(sym)
                                i += 1
                        continue
                rejected_candidates += 1
            elif valid:
                sec_kind = "annex" if kind == "annex" else ("terminal" if kind == "terminal" else "clause")
                heading_lines = [ln]
                k = i + 1
                if sec_kind == "annex":
                    # "Annex B" / "(normative)" / "Title ..." on consecutive lines (Directives Part 2 layout)
                    status = ""
                    m_status = re.match(r"^\((normative|informative)\)\s*(.*)$", title, re.I)
                    if m_status:
                        status, title = m_status.group(1).lower(), clean(m_status.group(2))
                    if k < n and _is_status_line(live[k].text) and live[k].page == ln.page:
                        status = live[k].text.strip("() ").lower()
                        heading_lines.append(live[k])
                        k += 1
                    if not title:
                        plain_heading = evidence == "toc"
                        title_lines, k2 = _collect_title(k, ln, allow_plain_first=plain_heading)
                        if title_lines:
                            title = clean(" ".join(l.text for l in title_lines))
                            heading_lines += title_lines
                            k = k2
                    if status:
                        title = f"{title} ({status})" if title else f"({status})"
                if sec_kind == "clause" and in_terms_clause() and len(parts) >= 2 and title and title[:1].islower():
                    sec_kind = "entry"
                sec = Section(side=side, number=number, title=title, level=len(parts), kind=sec_kind, heading_lines=heading_lines)
                if sec_kind == "entry":
                    sec.term = title
                if sec_kind == "clause" and TERMS_CLAUSE_TITLE_RE.search(title) and len(parts) <= 2:
                    terms_clause_numbers.add(number)
                push_section(sec)
                accepted += 1
                via_toc += int(evidence == "toc")
                i = k
                continue
            else:
                rejected_candidates += 1
        if current is None:
            front_matter.append(ln)
        else:
            current.paragraphs.append(Paragraph(kind="raw", text=ln.text, lines=[ln]))
        i += 1

    for sec in sections:
        sec.paragraphs = assemble_paragraphs(sec, lexicon)

    stats = {
        "side": side, "body_font_size": body_size, "sections": len(sections),
        "entries": sum(1 for s in sections if s.kind == "entry"),
        "annexes": sum(1 for s in sections if s.kind == "annex"),
        "rejected_heading_candidates": rejected_candidates, "front_matter_lines": len(front_matter),
        "headings_via_toc": via_toc, "toc_numbers": len(toc_numbers),
        "terms_clauses": sorted(terms_clause_numbers),
    }
    _log_event("STRUCTURE_EXTRACTED", **stats)
    return {"sections": sections, "front_matter": front_matter, "stats": stats, "body_font_size": body_size}


def _join_lone_markers(raw: list) -> list:
    """A list marker that PDF extraction puts on a line of its own ('•' set in the Symbol face, '–') is joined
    with the item text that follows it on the same baseline in the same block, so that '• a bridge method;' is
    one list item like every other list item - and never a short 'formula fragment' sent to the LLM."""
    out: list = []
    i = 0
    while i < len(raw):
        ln = raw[i]
        nxt = raw[i + 1] if i + 1 < len(raw) else None
        if (nxt is not None and LONE_MARKER_RE.match(ln.text) and nxt.page == ln.page and nxt.block_no == ln.block_no
                and abs(nxt.bbox[1] - ln.bbox[1]) < 2.0 and not LONE_MARKER_RE.match(nxt.text)):
            out.append(Line(side=ln.side, page=ln.page, block_no=ln.block_no, line_no=ln.line_no, text=clean(ln.text + " " + nxt.text),
                            bbox=(min(ln.bbox[0], nxt.bbox[0]), min(ln.bbox[1], nxt.bbox[1]), max(ln.bbox[2], nxt.bbox[2]), max(ln.bbox[3], nxt.bbox[3])),
                            size=nxt.size, bold=nxt.bold, y_ratio=nxt.y_ratio, page_height=nxt.page_height, removed=ln.removed,
                            italic=nxt.italic, words=list(ln.words) + list(nxt.words)))
            i += 2
            continue
        out.append(ln)
        i += 1
    return out


def assemble_paragraphs(sec: Section, lexicon: set[str]) -> list[Paragraph]:
    """Raw lines of a section -> paragraphs by PDF block boundaries and ISO 10241-1 / Directives markers."""
    raw = _join_lone_markers([p.lines[0] for p in sec.paragraphs if p.kind == "raw"])
    paras: list[Paragraph] = []
    cur_lines: list[Line] = []
    cur_kind = "body"
    cur_label = ""

    def flush():
        nonlocal cur_lines, cur_kind, cur_label
        if cur_lines:
            text = _join_lines([l.text for l in cur_lines], lexicon)
            paras.append(Paragraph(kind=cur_kind, text=text, lines=list(cur_lines), label=cur_label))
        cur_lines, cur_kind, cur_label = [], "body", ""

    prev: Optional[Line] = None
    for ln in raw:
        text = ln.text
        marker_kind, label = _paragraph_marker(text)
        new_block = prev is not None and (ln.page != prev.page or ln.block_no != prev.block_no)
        if marker_kind:
            flush()
            cur_kind, cur_label = marker_kind, label
            cur_lines = [ln]
        elif new_block or not cur_lines:
            flush()
            cur_lines = [ln]
            cur_kind = "body"
        else:
            cur_lines.append(ln)
        prev = ln
    flush()
    # The first body paragraph of a terminological entry is its definition.
    if sec.kind == "entry":
        for p in paras:
            if p.kind == "body":
                p.kind = "definition"
                break
    return paras


def _paragraph_marker(text: str) -> tuple[str, str]:
    m = NOTE_RE.match(text)
    if m and (text.startswith("NOTE") or text.startswith("Note ")):
        return "note", m.group(1) or "1"
    if SOURCE_RE.match(text) or (text.startswith("[") and SOURCE_ANY_RE.match(text)):
        return "source", ""
    m = CAPTION_RE.match(text)
    if m:
        return "caption", f"{m.group(1)} {m.group(2)}"
    m = LIST_ITEM_RE.match(text)
    if m:
        return "list", m.group(1)
    if EQUATION_NO_RE.search(text):          # "... (12)": an equation number at the end of the line (Directives Part 2)
        return "equation", EQUATION_NO_RE.search(text).group(1)
    return "", ""


def _join_lines(texts: list[str], lexicon: set[str]) -> str:
    out = texts[0] if texts else ""
    joins = 0
    for t in texts[1:]:
        out, joined = join_hyphenated(out, t, lexicon)
        joins += int(joined)
    return clean(out)


# ============================================================
# Stage 4 - OLD <-> NEW alignment
# ============================================================

def _tf(tokens_: list[str]) -> Counter:
    return Counter(tokens_)


def _cosine(a: Counter, b: Counter, idf: dict) -> float:
    if not a or not b:
        return 0.0
    num = sum(a[t] * b[t] * idf.get(t, 1.0) ** 2 for t in a if t in b)
    na = math.sqrt(sum((v * idf.get(t, 1.0)) ** 2 for t, v in a.items()))
    nb = math.sqrt(sum((v * idf.get(t, 1.0)) ** 2 for t, v in b.items()))
    return num / (na * nb) if na and nb else 0.0


def _title_key(sec: Section) -> str:
    """Title in comparison form. The annex status "(normative)" / "(informative)" is not part of the title: OLD C.1
    "Generation of current steps" and NEW "Annex C Generation of current steps (informative)" are the same text."""
    return norm_cmp(re.sub(r"\((?:normative|informative)\)", " ", sec.term or sec.title, flags=re.I))


def align_sections(old_secs: list[Section], new_secs: list[Section]) -> dict:
    """Three-stage section matching (number+title -> title -> TF-IDF cosine of body text).

    Follows the matching-then-edit-script scheme for hierarchically structured documents of
    Chawathe et al. (SIGMOD 1996), with domain knowledge: numbers are a strong but unstable key
    across editions, titles are stable, body similarity is the fallback. The stage-C threshold is
    calibrated on this document pair: midpoint between the low tail of stage-A pair similarities
    and the high tail of random non-pair similarities, never below SECTION_SIMILARITY_FLOOR.
    """
    pairs: list[dict] = []
    used_old: set[int] = set()
    used_new: set[int] = set()
    by_num_old = defaultdict(list)
    for i, s in enumerate(old_secs):
        by_num_old[s.number].append(i)
    old_index = {id(s): i for i, s in enumerate(old_secs)}
    new_index = {id(s): j for j, s in enumerate(new_secs)}
    partner_of_old: dict = {}

    def pair_same_number(j, ns, fuzzy: bool) -> bool:
        """Stage A: same number and the same title (fuzzy=False), or a near-same title (fuzzy=True, run only after
        stage B so that an exact title elsewhere wins: OLD 3.6.9 "type A evaluation" belongs to NEW 3.6.8 "type A
        evaluation", not to NEW 3.6.9 "type B evaluation" although that differs by one letter). The number is no
        evidence when the two parents carry the same number but were not paired (a restructured clause: OLD 6.4
        "Measurement of the test current" vs NEW 6.4 "Measurement of ripple amplitude"); such children are left to
        stage B, which pairs them under the right parents."""
        for i in by_num_old.get(ns.number, []):
            if i in used_old:
                continue
            os_ = old_secs[i]
            if (ns.parent is not None and os_.parent is not None and os_.parent.number == ns.parent.number
                    and partner_of_old.get(old_index.get(id(os_.parent))) != new_index.get(id(ns.parent))):
                continue
            same = _title_key(os_) == _title_key(ns) or (os_.kind == ns.kind == "clause" and not _title_key(ns))
            ratio = 1.0 if same else difflib.SequenceMatcher(None, _title_key(os_), _title_key(ns), autojunk=False).ratio()
            if same or (fuzzy and ratio >= 0.85):
                pairs.append({"old": i, "new": j, "stage": "A" if same else "A2", "score": round(ratio, 3), "moved": False})
                used_old.add(i)
                used_new.add(j)
                partner_of_old[i] = j
                return True
        return False

    for j, ns in enumerate(new_secs):
        pair_same_number(j, ns, fuzzy=False)
    # Stage B: same title, different number -> moved/renumbered. A title shared by several unused OLD sections
    # (IEC test-current clauses repeat "Requirements for an approved measuring system" in every clause) is
    # resolved by the tree: the candidate whose parent is the partner of the NEW section's parent (children are
    # matched under matched parents, Chawathe et al. 1996). NEW sections are visited in document order, so a
    # parent is paired before its children. Containers without body text are paired here as well.
    old_by_title = defaultdict(list)
    for i, s in enumerate(old_secs):
        if i not in used_old and _title_key(s):
            old_by_title[_title_key(s)].append(i)
    for j, ns in enumerate(new_secs):
        if j in used_new:
            continue
        key = _title_key(ns)
        cands = [i for i in old_by_title.get(key, []) if i not in used_old]
        if not key or len(key) < 4 or not cands:
            continue
        stage = "B"
        if len(cands) > 1:
            new_parent = new_index.get(id(ns.parent)) if ns.parent is not None else None
            cands = [i for i in cands if new_parent is not None and old_secs[i].parent is not None
                     and partner_of_old.get(old_index.get(id(old_secs[i].parent))) == new_parent]
            stage = "B-tree"
        if len(cands) != 1:
            continue
        i = cands[0]
        pairs.append({"old": i, "new": j, "stage": stage, "score": 1.0, "moved": True})
        used_old.add(i)
        used_new.add(j)
        partner_of_old[i] = j
    # Stage A2: same number, near-same title (>= 0.85) - only for what an exact title did not claim
    for j, ns in enumerate(new_secs):
        if j not in used_new:
            pair_same_number(j, ns, fuzzy=True)
    # Stage C: body-text similarity for the rest (TF-IDF cosine over section bodies)
    docs = [word_tokens(s.body_text() + " " + s.title) for s in old_secs] + \
           [word_tokens(s.body_text() + " " + s.title) for s in new_secs]
    df: Counter = Counter()
    for d in docs:
        for t in set(d):
            df[t] += 1
    n_docs = max(1, len(docs))
    idf = {t: math.log(1 + n_docs / (1 + c)) for t, c in df.items()}
    old_vec = [_tf(d) for d in docs[: len(old_secs)]]
    new_vec = [_tf(d) for d in docs[len(old_secs):]]

    def sim(i, j):
        return _cosine(old_vec[i], new_vec[j], idf)

    # calibration from stage A pairs vs random non-pairs
    pos = [sim(p["old"], p["new"]) for p in pairs if p["stage"].startswith("A") and old_secs[p["old"]].paragraphs and new_secs[p["new"]].paragraphs]
    neg = []
    if pos:
        import random
        rng = random.Random(7)
        a_pairs = [p for p in pairs if p["stage"].startswith("A")]
        for _ in range(min(400, len(a_pairs) * 3)):
            p = rng.choice(a_pairs)
            q = rng.choice(a_pairs)
            if p is not q:
                neg.append(sim(p["old"], q["new"]))
    if pos and neg:
        pos_sorted = sorted(pos)
        neg_sorted = sorted(neg)
        p_low = pos_sorted[max(0, int(len(pos_sorted) * 0.10))]
        n_high = neg_sorted[min(len(neg_sorted) - 1, int(len(neg_sorted) * 0.90))]
        threshold = max(SECTION_SIMILARITY_FLOOR, (p_low + n_high) / 2.0 if p_low > n_high else p_low)
    else:
        threshold = 0.5
    rem_old = [i for i in range(len(old_secs)) if i not in used_old and old_secs[i].paragraphs]
    rem_new = [j for j in range(len(new_secs)) if j not in used_new and new_secs[j].paragraphs]
    cands = []
    for i in rem_old:
        for j in rem_new:
            if old_secs[i].kind != new_secs[j].kind and {old_secs[i].kind, new_secs[j].kind} != {"clause", "entry"}:
                continue
            s = sim(i, j)
            if s >= threshold:
                cands.append((s, i, j))
    cands.sort(reverse=True)
    for s, i, j in cands:
        if i in used_old or j in used_new:
            continue
        pairs.append({"old": i, "new": j, "stage": "C", "score": round(s, 3), "moved": True})
        used_old.add(i)
        used_new.add(j)
    # Stage D: container sections (no own paragraphs, only children) cannot be matched by body text.
    # They are matched when they share the number, or when the majority of their matched children
    # landed under one unmatched NEW section (the children decide, as in tree matching by descendants).
    pair_old_to_new = {p["old"]: p["new"] for p in pairs}
    new_index = {id(s): j for j, s in enumerate(new_secs)}
    old_index = {id(s): i for i, s in enumerate(old_secs)}
    for i, os_ in enumerate(old_secs):
        if i in used_old or os_.paragraphs:
            continue
        target = None
        same_number = [j for j in range(len(new_secs)) if j not in used_new and new_secs[j].number == os_.number
                       and not new_secs[j].paragraphs and new_secs[j].kind == os_.kind
                       and (_title_key(new_secs[j]) == _title_key(os_) or not _title_key(os_) or not _title_key(new_secs[j]))]
        if len(same_number) == 1:
            target, stage = same_number[0], "D-number"
        else:
            votes: Counter = Counter()
            for child in os_.children:
                ci = old_index.get(id(child))
                nj = pair_old_to_new.get(ci)
                if nj is not None and new_secs[nj].parent is not None:
                    votes[new_index.get(id(new_secs[nj].parent))] += 1
            if votes:
                best, n_votes = votes.most_common(1)[0]
                if best is not None and best not in used_new and n_votes * 2 >= max(1, len(os_.children)):
                    target, stage = best, "D-children"
        if target is not None:
            pairs.append({"old": i, "new": target, "stage": stage, "score": 1.0, "moved": False})
            used_old.add(i)
            used_new.add(target)
            pair_old_to_new[i] = target
    # "moved" means the section now lives under a different parent (e.g. 6.2.1 -> 3.8.1). A number change
    # under the same parent (3.5.4 -> 3.5.3, A.3 -> A.2) is renumbering, which the renumber maps absorb.
    def parent_number(sec: Section) -> str:
        return sec.parent.number if sec.parent is not None else ""
    for p in pairs:
        o, nw = old_secs[p["old"]], new_secs[p["new"]]
        p["renumbered"] = o.number != nw.number
        p["moved"] = p["renumbered"] and parent_number(o) != parent_number(nw)
    deleted = [i for i in range(len(old_secs)) if i not in used_old]
    added = [j for j in range(len(new_secs)) if j not in used_new]
    pairs.sort(key=lambda p: p["new"])
    stats = {
        "old_sections": len(old_secs), "new_sections": len(new_secs),
        "stage_A": sum(1 for p in pairs if p["stage"].startswith("A")), "stage_B": sum(1 for p in pairs if p["stage"].startswith("B")),
        "stage_C": sum(1 for p in pairs if p["stage"] == "C"),
        "stage_D": sum(1 for p in pairs if p["stage"].startswith("D")), "deleted_sections": len(deleted),
        "added_sections": len(added), "stage_C_threshold": round(threshold, 3),
        "calibration_positive_n": len(pos), "calibration_negative_n": len(neg),
        "coverage_new": round(len(used_new) / max(1, len(new_secs)), 3),
    }
    _log_event("ALIGN_SECTIONS", **stats)
    return {"pairs": pairs, "deleted": deleted, "added": added, "stats": stats, "threshold": threshold}


def _text_sim(a: str, b: str) -> float:
    ta, tb = tokens(a), tokens(b)
    if not ta or not tb:
        return 1.0 if (a.strip() and norm_cmp(a) == norm_cmp(b)) else 0.0   # e.g. identical "____" rule lines
    return difflib.SequenceMatcher(None, ta, tb, autojunk=False).ratio()


def _para_sim(a: Paragraph, b: Paragraph) -> float:
    return _text_sim(a.text, b.text)


def merge_paragraphs(paras: list[Paragraph]) -> Paragraph:
    """Virtual paragraph for 2-1 / 1-2 alignments (one side split a paragraph the other side kept)."""
    if len(paras) == 1:
        return paras[0]
    return Paragraph(kind=paras[0].kind, text=clean(" ".join(p.text for p in paras)),
                     lines=[ln for p in paras for ln in p.lines], label=paras[0].label)


# Gale & Church (1993) needed a prior against 2-1 / 1-2 beads because they aligned by sentence LENGTH alone. Here
# the beads are scored by text similarity, so a merge / split is chosen only when the merged text is more similar
# than either part alone; no hand-chosen penalty is added.
MERGE_PENALTY = 0.0


def _otsu_split(values: list[float]) -> tuple[Optional[float], float]:
    """Otsu (1979) threshold on a one-dimensional sample: the split that maximises the between-class variance.
    Returns (threshold, separability eta in 0..1); (None, 0.0) when the sample cannot be split."""
    v = sorted(values)
    n = len(v)
    if n < 2 or v[0] == v[-1]:
        return None, 0.0
    total = sum(v)
    mean = total / n
    var = sum((x - mean) ** 2 for x in v) / n
    best, best_t, run = -1.0, None, 0.0
    for k in range(1, n):
        run += v[k - 1]
        if v[k - 1] == v[k]:
            continue
        m0, m1 = run / k, (total - run) / (n - k)
        between = k * (n - k) * (m0 - m1) ** 2 / float(n * n)
        if between > best:
            best, best_t = between, (v[k - 1] + v[k]) / 2.0
    return best_t, (best / var if var > 0 else 0.0)


def _valley_threshold(values: list[float]) -> tuple[Optional[float], Optional[float], float]:
    """Valley-seeking threshold for a two-group sample.

    Otsu's split provides the two class means; the threshold is the minimum of a Gaussian kernel density estimate
    (Silverman's 1986 rule-of-thumb bandwidth) between those means. Otsu's own threshold is biased towards the
    larger and tighter class - here the cluster of nearly identical paragraphs - whereas the density valley sits
    where the two groups actually separate. Returns (valley, otsu, otsu_eta); (None, None, 0) when unsplittable.
    """
    otsu, eta = _otsu_split(values)
    if otsu is None:
        return None, None, 0.0
    lo = [x for x in values if x < otsu]
    hi = [x for x in values if x >= otsu]
    if not lo or not hi:
        return otsu, otsu, eta
    m0, m1 = sum(lo) / len(lo), sum(hi) / len(hi)
    v = sorted(values)
    n = len(v)
    mean = sum(v) / n
    sd = (sum((x - mean) ** 2 for x in v) / n) ** 0.5
    iqr = v[int(0.75 * (n - 1))] - v[int(0.25 * (n - 1))]
    spread = min(sd, iqr / 1.34) if iqr > 0 else sd
    h = 0.9 * spread * n ** (-0.2)
    if h <= 0:
        return otsu, otsu, eta
    best_x, best_d = otsu, float("inf")
    steps = 200
    for k in range(steps + 1):
        x = m0 + (m1 - m0) * k / steps
        d = sum(math.exp(-0.5 * ((x - y) / h) ** 2) for y in v)
        if d < best_d:
            best_d, best_x = d, x
    return best_x, otsu, eta


def calibrate_paragraph_threshold(old_secs: list[Section], new_secs: list[Section], pairs: list[dict]) -> dict:
    """Per-pair calibration of the paragraph-alignment threshold, the way stage C calibrates sections.

    Sample: inside the stage-A section pairs (same number and title - the sections that certainly correspond), the
    best-match similarity of every paragraph against the other side, leaving out identical paragraphs (they say
    nothing about where "modified" ends and "unrelated" begins) and formula fragments. The sample has two groups -
    paragraphs with a modified counterpart and paragraphs with none - and the threshold is the density valley
    between them (_valley_threshold: Otsu split for the two class means, kernel density minimum between them).
    Chance level: the 90th percentile of random paragraph pairs from different sections; the threshold never goes
    below it. Falls back to PARAGRAPH_MATCH_THRESHOLD only when the pair offers no sample. Everything is logged
    (ALIGN_PARAGRAPH_CALIBRATION) and reported in the metrics.
    """
    sample: list[float] = []
    pool: list[tuple[int, Paragraph]] = []
    for p in pairs:
        if p["stage"] != "A":
            continue
        op = [x for x in old_secs[p["old"]].paragraphs if not _is_fragment(x)]
        np_ = [x for x in new_secs[p["new"]].paragraphs if not _is_fragment(x)]
        if not op or not np_:
            continue
        sims = [[_text_sim(a.text, b.text) for b in np_] for a in op]
        for i in range(len(op)):
            best = max(sims[i])
            if best < 0.999:
                sample.append(best)
        for j in range(len(np_)):
            best = max(sims[i][j] for i in range(len(op)))
            if best < 0.999:
                sample.append(best)
        pool.extend((p["old"], a) for a in op)
    neg: list[float] = []
    if len(pool) >= 2:
        import random
        rng = random.Random(13)
        for _ in range(min(600, len(pool) * 2)):
            (sa, a), (sb, b) = rng.choice(pool), rng.choice(pool)
            if sa != sb:
                neg.append(_text_sim(a.text, b.text))
    chance = sorted(neg)[min(len(neg) - 1, int(len(neg) * 0.90))] if neg else 0.0
    valley, otsu, eta = _valley_threshold(sample)
    if valley is None:
        threshold, source = PARAGRAPH_MATCH_THRESHOLD, "fallback"
    else:
        threshold, source = max(valley, chance), ("valley" if valley >= chance else "chance")
    stats = {"paragraph_threshold": round(threshold, 3), "paragraph_threshold_source": source,
             "paragraph_valley": round(valley, 3) if valley is not None else None,
             "paragraph_otsu": round(otsu, 3) if otsu is not None else None, "paragraph_otsu_eta": round(eta, 3),
             "paragraph_chance_p90": round(chance, 3), "paragraph_calibration_n": len(sample), "paragraph_negative_n": len(neg)}
    _log_event("ALIGN_PARAGRAPH_CALIBRATION", **stats)
    return {"threshold": threshold, "stats": stats}


def align_paragraphs(old_paras: list[Paragraph], new_paras: list[Paragraph], threshold: Optional[float] = None) -> list[tuple]:
    """Dynamic-programming alignment with 1-1, 1-0, 0-1, 2-1 and 1-2 beads maximising sum(sim - threshold).

    Classic sentence-alignment DP (Gale & Church 1993; Barzilay & Elhadad 2003 for monolingual
    revisions); similarity is the Ratcliff/Obershelp ratio on tokens (Python difflib). Beads below the
    threshold (calibrated per document pair by calibrate_paragraph_threshold) are left unmatched.
    Returns [(old_indices, new_indices, sim)] where either index list may be empty (deletion / insertion).
    """
    T = PARAGRAPH_MATCH_THRESHOLD if threshold is None else threshold
    n, m = len(old_paras), len(new_paras)
    if n == 0:
        return [([], [j], 0.0) for j in range(m)]
    if m == 0:
        return [([i], [], 0.0) for i in range(n)]
    band = max(6, abs(n - m) + 3)
    cache: dict = {}

    def sim(oi: tuple, nj: tuple) -> float:
        key = (oi, nj)
        if key not in cache:
            a = " ".join(old_paras[i].text for i in oi)
            b = " ".join(new_paras[j].text for j in nj)
            cache[key] = _text_sim(a, b)
        return cache[key]

    NEG = -1e9
    dp = [[NEG] * (m + 1) for _ in range(n + 1)]
    back = [[None] * (m + 1) for _ in range(n + 1)]
    dp[0][0] = 0.0
    for i in range(n + 1):
        for j in range(m + 1):
            if dp[i][j] == NEG:
                continue
            cur = dp[i][j]
            # Plain deletion / insertion moves use >=: on a tie they override a 2-1 / 1-2 bead reached earlier, so a
            # merge or split is kept only when it is STRICTLY better than aligning 1-1 (e.g. a token-less line such
            # as "__" must not be absorbed into the neighbouring paragraph).
            if i < n and cur >= dp[i + 1][j]:
                dp[i + 1][j] = cur
                back[i + 1][j] = (i, j, (i,), ())
            if j < m and cur >= dp[i][j + 1]:
                dp[i][j + 1] = cur
                back[i][j + 1] = (i, j, (), (j,))
            if abs(i - j) > band:
                continue
            if i < n and j < m:
                gain = sim((i,), (j,)) - T
                if gain > 0 and cur + gain > dp[i + 1][j + 1]:
                    dp[i + 1][j + 1] = cur + gain
                    back[i + 1][j + 1] = (i, j, (i,), (j,))
            if i + 1 < n and j < m:
                gain = sim((i, i + 1), (j,)) - T - MERGE_PENALTY
                if gain > 0 and cur + gain > dp[i + 2][j + 1]:
                    dp[i + 2][j + 1] = cur + gain
                    back[i + 2][j + 1] = (i, j, (i, i + 1), (j,))
            if i < n and j + 1 < m:
                gain = sim((i,), (j, j + 1)) - T - MERGE_PENALTY
                if gain > 0 and cur + gain > dp[i + 1][j + 2]:
                    dp[i + 1][j + 2] = cur + gain
                    back[i + 1][j + 2] = (i, j, (i,), (j, j + 1))
    out = []
    i, j = n, m
    while (i, j) != (0, 0):
        pi, pj, oi, nj = back[i][j]
        out.append((list(oi), list(nj), sim(oi, nj) if oi and nj else 0.0))
        i, j = pi, pj
    out.reverse()
    
    # is the 'replace' block of a standard diff with one paragraph on each side: the same slot in both editions.
    # It becomes a 1-1 bead whatever its similarity, so a heavily rewritten paragraph is reported as a modification
    # (one card, word boxes where possible) instead of a deletion plus an insertion with a band on each side.
    merged: list = []
    k = 0
    while k < len(out):
        if out[k][0] and out[k][1]:
            merged.append(out[k])
            k += 1
            continue
        run_end = k
        while run_end < len(out) and not (out[run_end][0] and out[run_end][1]):
            run_end += 1
        run = out[k:run_end]
        dels = [b for b in run if b[0]]
        ins = [b for b in run if b[1]]
        if len(dels) == 1 and len(ins) == 1 and len(dels[0][0]) == 1 and len(ins[0][1]) == 1:
            oi, nj = dels[0][0], ins[0][1]
            merged.append((list(oi), list(nj), sim(tuple(oi), tuple(nj))))
        else:
            merged.extend(run)
        k = run_end
    return merged


# ============================================================
# Stage 5 - Hunks and rule-based editorial tagging
# ============================================================

# Editorial-equivalence normalisers. Each one is an editorial convention that changed between
# ISO/IEC Directives Part 2 editions or is prescribed by ISO 10241-1 for terminological entries;
# none of them alters technical meaning.
def _editorial_norm(text: str) -> str:
    t = norm_cmp(text)
    t = re.sub(r"\bnote\s*(\d*)\s+to\s+entry\s*[:\-]?", lambda m: f"note {m.group(1) or '1'}", t)   # ISO 10241-1 note form
    t = re.sub(r"\bnote\s*[:\-]", "note 1", t)
    t = re.sub(r"\bnote\b(?!\s*\d)", "note 1", t)
    t = re.sub(r"\[\s*source\s*:\s*", "[", t)                                                         # [SOURCE: X] vs [X]
    # d.c. -> dc, r.m.s. -> rms: ISO/IEC Directives Part 2:2021, 8.4 ("Any abbreviated term should be in uppercase
    # letters, without a full stop after each letter"); IEC 60050-131 note: "AC" is preferred to "a.c." in English.
    t = re.sub(r"\b([a-z])\.([a-z])\.(?:([a-z])\.)?", lambda m: "".join(x for x in m.groups() if x), t)
    t = re.sub(r"\bthis (?:international standard|standard|technical specification|technical report|part of iec \d+(?:-\d+)*)\b", "this document", t)  # Directives 2016+: "this document"
    t = re.sub(r"\b(?:clause|subclause)\s+(?=\d)", "", t)                                             # "Clause 5" vs "5"
    # "IEC 60060" vs "60060" is deliberately NOT normalised: no editorial rule prescribes dropping the organisation
    # from a document designation, so such a difference goes to the LLM like any other.
    # Only typographic punctuation is neutral: full stops, commas, semicolons, colons, question / exclamation marks,
    # quotation marks, apostrophes, hyphens and dashes, bullets, underscores. Mathematical signs and unit-like
    # symbols (ISO 80000-1/-2: + − × · / = < > ≤ ≥ ± % ‰ ° ∑ √ ...) and brackets carry technical content, so a
    # difference in them is never editorial by rule; the LLM judges it.
    t = re.sub(r"(?<=\d)\.(?=\d)", ",", t)      # decimal sign: Directives Part 2:2021, 9.1 (comma on the line)
    t = re.sub(r"[.,;:!?'\"“”‘’«»‹›\-–—•_]", " ", t)
    return " ".join(TOKEN_RE.findall(t))       # spacing around symbols ("VN/VX" vs "VN / VX") is typographic


# Provision types and their verbal forms, taken verbatim from ISO/IEC Directives Part 2:2021 (9th ed.), Clause 7,
# Tables 3-7 (preferred verbal form + "equivalent phrases or expressions for use in certain cases"). One row = one
# provision type. By the Directives' own definition a wording change inside a row keeps the provision type
# (requirement, recommendation, permission, possibility/capability, external constraint) and is therefore
# editorial; a change from one row to another changes the provision type and goes to the LLM as VERBAL_FORM.
# The "need not" row is Table 5 of the 2018 (8th) edition (negative permission, withdrawn in 2021); older editions
# were drafted under it. Expressions with a gap ("only ... is permitted", "is required that ... be not",
# "no ... is required") are not matched by code and remain CONTENT, i.e. the LLM judges them.
# Nothing outside these tables is added here (project rule: no hand-made lists; what the tables do not cover
# goes to the LLM).
PROVISION_FORMS = [
    ("vfreqnot", ["shall not", "is not allowed", "is not permitted", "is not acceptable", "is not permissible",
                  "is required to be not", "is not to be", "do not"]),                       # Table 3, 2nd row
    ("vfreq", ["shall", "is required to", "it is required that", "has to", "it is necessary", "is to"]),  # Table 3
    ("vfrecnot", ["should not", "it is not recommended that", "ought not to"]),              # Table 4, 2nd row
    ("vfrec", ["should", "it is recommended that", "ought to"]),                              # Table 4
    ("vfpermnot", ["need not", "it is not required that"]),                                  # Table 5 (2018 ed.)
    ("vfperm", ["may", "is permitted", "is allowed", "is permissible"]),                      # Table 5
    ("vfpossnot", ["cannot", "be unable to", "there is no possibility of", "it is not possible to"]),  # Table 6, 2nd row
    ("vfposs", ["can", "be able to", "there is a possibility of", "it is possible to"]),      # Table 6
    ("vfext", ["must"]),                                                                      # Table 7
]
# Negated / longer rows are listed first so that "shall not" is never read as "shall" + "not".
PROVISION_PATTERNS = [(tok, re.compile(r"\b(?:" + "|".join(re.escape(ph) for ph in phrases) + r")\b"))
                      for tok, phrases in PROVISION_FORMS]
PROVISION_TOKENS = {tok for tok, _ in PROVISION_FORMS}


def _provision_norm(text: str) -> str:
    """Editorial normalisation plus replacement of every Directives verbal form by its provision-row token."""
    t = _editorial_norm(text)
    for tok, pat in PROVISION_PATTERNS:
        t = pat.sub(tok, t)
    return t


def _is_fragment(para: Paragraph) -> bool:
    """Formula / figure pieces that PDF text extraction renders as symbol soup ('= + + × =', 'Y', '80').

    Two document-derived criteria, no thresholds: (1) every line of the paragraph sits inside a vector drawing or
    image of the page (Line.in_graphic, from PyMuPDF's own drawing clusters and image blocks) - the document
    itself places formula and figure text there; (2) the text contains no word at all, a word being a token of
    two or more letters (ISO 80000-1 sets quantity symbols as single letters, so a lone letter is a symbol).
    Ordinary text keeps its class however short it is ('where', '• a bridge method;', 'This standard:').
    Equation and table content is the weakest part of PDF text extraction (Bast & Korzen 2017). The tag only
    changes how such differences are presented: they are merged per section (_merge_fragment_hunks), sent to the
    LLM with an extraction warning like every other difference in a FOREWORD region or in the full read-through,
    and listed per section for a visual check. It never decides whether a difference reaches the LLM.
    """
    if para.lines and all(ln.in_graphic for ln in para.lines):
        return True
    return _is_symbol_soup(para.text)


# ISO 80000-2:2019 (Quantities and units - Part 2: Mathematics) prints the standard functions and operators in upright
# type as symbols: trigonometric and hyperbolic functions and their inverses, exponential and logarithmic functions,
# limits and extremes, sign, determinant, error function. Such a token is a symbol, not a word, so a formula line

# div, rot, tr) are deliberately left out of the list.
MATH_FUNCTION_SYMBOLS = frozenset(
    "sin cos tan cot sec csc arcsin arccos arctan arccot arcsec arccsc sinh cosh tanh coth sech csch arsinh arcosh "
    "artanh arcoth exp ln lg lb log lim max min sup inf sgn det erf erfc".split())


def _is_symbol_soup(text: str) -> bool:
    """Text without a single word (a token of two or more letters that is not an ISO 80000-2 function symbol):
    symbols, numbers, operators and function names only."""
    return not any(re.match(r"^[a-z]{2,}$", t) and t not in MATH_FUNCTION_SYMBOLS for t in tokens(text))


def _provision_type_changed_only(old_norm: str, new_norm: str) -> bool:
    """True when the provision-normalised texts differ only in provision-row tokens (e.g. shall -> should)."""
    pa, pb = old_norm.split(), new_norm.split()
    sm = difflib.SequenceMatcher(None, pa, pb, autojunk=False)
    changed = [w for tag, i1, i2, j1, j2 in sm.get_opcodes() if tag != "equal" for w in pa[i1:i2] + pb[j1:j2]]
    return bool(changed) and all(w in PROVISION_TOKENS for w in changed)


@dataclass
class Hunk:
    hunk_id: str
    change_type: str              # MODIFY | ADD | DELETE | MOVE
    unit: str                     # paragraph | section
    old_section: Optional[Section]
    new_section: Optional[Section]
    old_para: Optional[Paragraph]
    new_para: Optional[Paragraph]
    old_text: str
    new_text: str
    kind: str                     # paragraph kind (definition, note, source, body, caption, fragment, ...)
    editorial_only: bool
    renumber_only: bool
    similarity: float
    moved_section: bool
    old_changed_anchors: list = field(default_factory=list)
    new_changed_anchors: list = field(default_factory=list)
    default_bucket: str = ""
    diff_ops: list = field(default_factory=list)
    verbal_form_only: bool = False
    fragment: bool = False
    candidate_buckets: list = field(default_factory=list)
    member_count: int = 1          # > 1 for a merged formula/table-fragment hunk (see _merge_fragment_hunks)
    diff_ops_total: int = 0        # number of diff operations before DIFF_OPS_CAP
    old_changed_words: list = field(default_factory=list)   # word runs absent from the other side (exact-position boxes)
    new_changed_words: list = field(default_factory=list)
    systematic_only: bool = False   # every difference is a replacement recurring across the document (mark_systematic_substitutions)
    systematic_pairs: list = field(default_factory=list)
    vlm: Optional[dict] = None      # vision-model reading of a formula/figure fragment (vlm_compare_fragments), reference only

    @property
    def rule_class(self) -> str:
        """Deterministic pre-classification used for routing and reporting. Equality after the cited normalisations
        (EDITORIAL / RENUMBER) comes first: a formula fragment that differs only in punctuation has nothing to judge."""
        if self.editorial_only:
            return "EDITORIAL"
        if self.renumber_only:
            return "RENUMBER"
        if self.systematic_only:
            return "SYSTEMATIC"
        if self.fragment:
            return "FRAGMENT"
        if self.verbal_form_only:
            return "VERBAL_FORM"
        return "CONTENT"

    def to_payload(self, max_chars: int = TRIAGE_HUNK_CHARS) -> dict:
        cap = max_chars
        payload = {
            "hunk_id": self.hunk_id,
            "change_type": self.change_type,
            "unit": self.unit,
            "kind": self.kind,
            "old_location": (self.old_section.path() + (f" [{self.old_section.term}]" if self.old_section.term else "")) if self.old_section else "",
            "new_location": (self.new_section.path() + (f" [{self.new_section.term}]" if self.new_section.term else "")) if self.new_section else "",
            "old_pages": sorted({a["page"] for a in self.old_changed_anchors}) or ([self.old_section.page_range()[0]] if self.old_section and self.old_text else []),
            "new_pages": sorted({a["page"] for a in self.new_changed_anchors}) or ([self.new_section.page_range()[0]] if self.new_section and self.new_text else []),
            "old_text": _cut(self.old_text, cap),
            "new_text": _cut(self.new_text, cap),
            "rule_class": self.rule_class,
            "section_moved": self.moved_section,
            "default_foreword_item": self.default_bucket,
            "candidate_foreword_items": self.candidate_buckets,
            "diff_ops": self.diff_ops,
            "diff_ops_total": max(self.diff_ops_total, len(self.diff_ops)),
        }
        if self.diff_ops_total > len(self.diff_ops):
            payload["diff_ops_truncated"] = True       # the texts above still show every difference
        if self.systematic_pairs:
            payload["systematic_substitutions"] = self.systematic_pairs   # replacements recurring across the document
        if self.fragment:
            payload["extraction_note"] = (
                f"FRAGMENT: formula/table text as extracted from the PDF ({self.member_count} fragment(s) of this section merged); "
                "symbols may be garbled, split or out of order. Judge whether the formula/table content changed as the item "
                "declares; if the text is unreadable set needs_context=true instead of guessing.")
        if self.vlm and self.vlm.get("same"):
            payload["visual_reading"] = {
                "source": f"vision model {self.vlm.get('model', '')} reading the rendered OLD/NEW formula - NOT verified; prefer it "
                          "over the garbled token text above, but do not treat it as ground truth",
                "same": self.vlm["same"], "changes": self.vlm.get("changes", []),
                "old_transcription": self.vlm.get("old_transcription", ""), "new_transcription": self.vlm.get("new_transcription", ""),
            }
        return payload


def _changed_line_anchors(para: Paragraph, other_text: str) -> list[dict]:
    """Lines of `para` that contain tokens absent from the other side (for tight highlighting). A changed heading
    is shown whole (number line and wrapped title lines), not just the line that holds the differing token."""
    other = set(tokens(other_text))
    hit_lines = []
    if para.kind == "heading_text" and other_text:
        hit_lines = list(para.lines)
    else:
        for ln in para.lines:
            toks = tokens(ln.text)
            if any(t not in other for t in toks if re.match(r"[^\W_]", t)):
                hit_lines.append(ln)
    if not hit_lines:
        hit_lines = list(para.lines)
    out = []
    for page in sorted({ln.page for ln in hit_lines}):
        boxes = [ln.bbox for ln in hit_lines if ln.page == page]
        out.append({"page": page, "bbox": [min(b[0] for b in boxes), min(b[1] for b in boxes),
                                            max(b[2] for b in boxes), max(b[3] for b in boxes)]})
    return out


WORD_BOX_MAX_SHARE = 0.6      # above this share of changed words the paragraph box is the honest display
WORD_BOX_JOIN_GAP = 6.0       # points; neighbouring changed words closer than this form one run
DIFF_OPS_CAP = 40             # token-diff operations kept per hunk (diff_ops_total records the real number)


def _changed_word_anchors(para: Paragraph, other_text: str) -> list[dict]:
    """Runs of words of `para` whose tokens are absent from the other side, as boxes: the exact place of a
    difference inside its line. Empty for whole-paragraph additions and deletions, for lines without word
    geometry, and for paragraphs rewritten beyond WORD_BOX_MAX_SHARE (there the line box says it better)."""
    if not other_text:
        return []
    other = set(tokens(other_text))
    runs: list[dict] = []
    total = changed = 0
    for ln in para.lines:
        cur = None
        for x0, y0, x1, y1, text in ln.words:
            toks = [t for t in tokens(text) if re.match(r"[^\W_]", t)]
            if not toks:
                cur = None
                continue
            total += 1
            stem = norm_cmp(text).rstrip("-")
            unchanged = all(t in other for t in toks) or (
                text.endswith("-") and len(stem) >= 3 and any(o.startswith(stem) for o in other))   # hyphenated at line end
            if unchanged:
                cur = None
                continue
            changed += 1
            if cur is not None and cur["page"] == ln.page and x0 - cur["bbox"][2] <= WORD_BOX_JOIN_GAP:
                cur["bbox"] = [cur["bbox"][0], min(cur["bbox"][1], y0), max(cur["bbox"][2], x1), max(cur["bbox"][3], y1)]
            else:
                cur = {"page": ln.page, "bbox": [x0, y0, x1, y1]}
                runs.append(cur)
    if not runs or (total and changed / total > WORD_BOX_MAX_SHARE):
        return []
    return runs


def _renumber_map(old_secs, new_secs, pairs) -> dict[str, str]:
    """old clause number -> new clause number for aligned sections (used to neutralise cross-reference renumbering)."""
    mp = {}
    for p in pairs:
        o, nw = old_secs[p["old"]], new_secs[p["new"]]
        if o.number != nw.number and re.match(r"^[A-Z0-9]", o.number):
            mp[o.number] = nw.number
    return mp


_CAPTION_LABEL_RE = re.compile(r"\b(Figure|Table)\s+([A-Z]?\.?\d+[a-z]?)\b", re.I)
_EQUATION_LABEL_RE = re.compile(r"\((\d{1,3})\)")


def _label_maps_from_alignment(section_alignments: list[tuple]) -> tuple[dict, dict]:
    """Figure/Table and equation renumbering maps from aligned caption / equation paragraphs.

    Captions and equation numbers are renumbered wholesale when content is inserted; a reference such
    as 'see Figure 15' -> 'see Figure 20' is then not a technical change. The maps are learned from the
    document pair itself (aligned caption paragraphs), never hard-coded.
    """
    cap_map: dict[str, str] = {}
    eq_map: dict[str, str] = {}
    for os_, ns, beads in section_alignments:
        for oi, nj, s in beads:
            if not oi or not nj:
                continue
            op, np_ = merge_paragraphs([os_.paragraphs[k] for k in oi]), merge_paragraphs([ns.paragraphs[k] for k in nj])
            if op.kind == "caption" and np_.kind == "caption":
                mo, mn = _CAPTION_LABEL_RE.match(op.text), _CAPTION_LABEL_RE.match(np_.text)
                if mo and mn and mo.group(1).lower() == mn.group(1).lower() and mo.group(2) != mn.group(2):
                    cap_map[f"{mo.group(1).lower()} {mo.group(2).lower()}"] = f"{mn.group(1).lower()} {mn.group(2).lower()}"
            if op.kind == "equation" and np_.kind == "equation" and op.label and np_.label and op.label != np_.label:
                eq_map[op.label] = np_.label
    return cap_map, eq_map


def _apply_renumber(text: str, mp: dict[str, str], cap_map: Optional[dict] = None, eq_map: Optional[dict] = None) -> str:
    out = text
    if cap_map:
        out = _CAPTION_LABEL_RE.sub(lambda m: cap_map.get(f"{m.group(1).lower()} {m.group(2).lower()}", m.group(0)), out)
    if eq_map:
        out = _EQUATION_LABEL_RE.sub(lambda m: f"({eq_map.get(m.group(1), m.group(1))})", out)
    if mp:
        out = re.sub(r"\b(?:Annex\s+[A-Z]|[A-Z](?:\.\d+)+|\d+(?:\.\d+)+|\d{1,2})\b", lambda m: mp.get(m.group(0), m.group(0)), out)
    return out


def build_hunks(old_struct: dict, new_struct: dict, alignment: dict) -> list[Hunk]:
    old_secs, new_secs = old_struct["sections"], new_struct["sections"]
    pairs = alignment["pairs"]
    renum = _renumber_map(old_secs, new_secs, pairs)
    cal = calibrate_paragraph_threshold(old_secs, new_secs, pairs)
    alignment["paragraph_threshold"] = cal["threshold"]
    alignment.setdefault("stats", {}).update(cal["stats"])
    hunks: list[Hunk] = []
    seq = 0

    def next_id():
        nonlocal seq
        seq += 1
        return f"H{seq:04d}"

    # Paragraph alignment once per section pair; caption/equation renumbering maps are learned from it.
    section_alignments = []
    for p in pairs:
        os_, ns = old_secs[p["old"]], new_secs[p["new"]]
        section_alignments.append((os_, ns, align_paragraphs(os_.paragraphs, ns.paragraphs, cal["threshold"])))
    cap_map, eq_map = _label_maps_from_alignment(section_alignments)
    maps = (renum, cap_map, eq_map)

    for p, (os_, ns, beads) in zip(pairs, section_alignments):
        moved = bool(p["moved"])
        if moved:
            # The relocation itself is one hunk (title changes ride along in its text); it is always a
            # CONTENT-class hunk so that a FOREWORD "moved into ..." item can collect it.
            hp_old = Paragraph(kind="heading_text", text=os_.number + " " + (os_.term or os_.title), lines=list(os_.heading_lines))
            hp_new = Paragraph(kind="heading_text", text=ns.number + " " + (ns.term or ns.title), lines=list(ns.heading_lines))
            mv = _make_hunk(next_id(), "MOVE", "section", os_, ns, hp_old, hp_new, maps, moved)
            mv.editorial_only = False
            mv.renumber_only = False
            mv.verbal_form_only = False
            hunks.append(mv)
        elif norm_cmp(os_.term or os_.title) != norm_cmp(ns.term or ns.title) and (os_.title or ns.title):
            # Heading/term change of a section that stayed in place
            hp_old = Paragraph(kind="heading_text", text=(os_.term or os_.title), lines=list(os_.heading_lines))
            hp_new = Paragraph(kind="heading_text", text=(ns.term or ns.title), lines=list(ns.heading_lines))
            hunks.append(_make_hunk(next_id(), "MODIFY", "paragraph", os_, ns, hp_old, hp_new, maps, moved))
        for oi, nj, s in beads:
            if oi and nj:
                op, np_ = merge_paragraphs([os_.paragraphs[k] for k in oi]), merge_paragraphs([ns.paragraphs[k] for k in nj])
                if norm_cmp(op.text) == norm_cmp(np_.text):
                    continue
                hunks.append(_make_hunk(next_id(), "MODIFY", "paragraph", os_, ns, op, np_, maps, moved, s))
            elif oi:
                hunks.append(_make_hunk(next_id(), "DELETE", "paragraph", os_, ns, os_.paragraphs[oi[0]], None, maps, moved))
            else:
                hunks.append(_make_hunk(next_id(), "ADD", "paragraph", os_, ns, None, ns.paragraphs[nj[0]], maps, moved))
    for i in alignment["deleted"]:
        os_ = old_secs[i]
        if not os_.paragraphs and not os_.title:
            continue
        hp = Paragraph(kind="heading_text", text=os_.number + " " + (os_.term or os_.title) + "\n" + os_.body_text(),
                       lines=list(os_.heading_lines) + [ln for pp in os_.paragraphs for ln in pp.lines])
        hunks.append(_make_hunk(next_id(), "DELETE", "section", os_, None, hp, None, maps, False))
    for j in alignment["added"]:
        ns = new_secs[j]
        if not ns.paragraphs and not ns.title:
            continue
        hp = Paragraph(kind="heading_text", text=ns.number + " " + (ns.term or ns.title) + "\n" + ns.body_text(),
                       lines=list(ns.heading_lines) + [ln for pp in ns.paragraphs for ln in pp.lines])
        hunks.append(_make_hunk(next_id(), "ADD", "section", None, ns, None, hp, maps, False))
    # Tables: cell-wise comparison inside aligned sections; whole tables in unmatched sections.
    table_hunks = 0
    for p, (os_, ns, beads) in zip(pairs, section_alignments):
        for h in _table_hunks(os_, ns, cap_map, next_id, bool(p["moved"])):
            hunks.append(h)
            table_hunks += 1
    for i in alignment["deleted"]:
        for t in old_secs[i].tables:
            hunks.append(_table_hunk_from(next_id(), "DELETE", old_secs[i], None, t, None, [], False))
            table_hunks += 1
    for j in alignment["added"]:
        for t in new_secs[j].tables:
            hunks.append(_table_hunk_from(next_id(), "ADD", None, new_secs[j], None, t, [], False))
            table_hunks += 1
    alignment["systematic_pairs"] = mark_systematic_substitutions(hunks)
    hunks = _merge_fragment_hunks(hunks, next_id)
    stats = {
        "hunks": len(hunks),
        "fragment_members": sum(h.member_count for h in hunks if h.fragment),
        "modify": sum(1 for h in hunks if h.change_type == "MODIFY"),
        "add": sum(1 for h in hunks if h.change_type == "ADD"),
        "delete": sum(1 for h in hunks if h.change_type == "DELETE"),
        "move": sum(1 for h in hunks if h.change_type == "MOVE"),
        "table_hunks": table_hunks,
        "rule_classes": dict(Counter(h.rule_class for h in hunks)),
        "renumber_map_size": len(renum), "caption_map_size": len(cap_map), "equation_map_size": len(eq_map),
    }
    _log_event("HUNKS_BUILT", **stats)
    return hunks


def _align_tables(old_tables: list[TableBlock], new_tables: list[TableBlock], cap_map: dict) -> tuple[list, list, list]:
    """Pair tables of an aligned section pair: by caption label (through the learned caption map), then by
    cell-text similarity (>= 0.5). Returns (pairs, unmatched_old, unmatched_new)."""
    pairs, used_new = [], set()
    for i, ot in enumerate(old_tables):
        if not ot.label:
            continue
        target = cap_map.get(ot.label, ot.label)
        for j, nt in enumerate(new_tables):
            if j not in used_new and nt.label == target:
                pairs.append((i, j))
                used_new.add(j)
                break
    matched_old = {i for i, _ in pairs}
    for i, ot in enumerate(old_tables):
        if i in matched_old:
            continue
        best, best_s = None, 0.0
        for j, nt in enumerate(new_tables):
            if j in used_new:
                continue
            s = _text_sim(ot.flat_text(), nt.flat_text())
            if s > best_s:
                best, best_s = j, s
        if best is not None and best_s >= 0.5:
            pairs.append((i, best))
            used_new.add(best)
            matched_old.add(i)
    return pairs, [i for i in range(len(old_tables)) if i not in matched_old], [j for j in range(len(new_tables)) if j not in used_new]


def _table_cell_diff(ot: TableBlock, nt: TableBlock) -> list[dict]:
    """Changed cells. Same shape -> position-wise; different shape -> row alignment by difflib, then cells."""
    diffs = []
    if ot.shape == nt.shape:
        for r, (ro, rn) in enumerate(zip(ot.cells, nt.cells)):
            for c, (a, b) in enumerate(zip(ro, rn)):
                if norm_cmp(a) != norm_cmp(b):
                    diffs.append({"old_rc": (r, c), "new_rc": (r, c), "old": a, "new": b})
        return diffs
    old_rows = [norm_cmp(" | ".join(r)) for r in ot.cells]
    new_rows = [norm_cmp(" | ".join(r)) for r in nt.cells]
    sm = difflib.SequenceMatcher(None, old_rows, new_rows, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        for k in range(max(i2 - i1, j2 - j1)):
            oi = i1 + k if i1 + k < i2 else None
            nj = j1 + k if j1 + k < j2 else None
            ro = ot.cells[oi] if oi is not None else []
            rn = nt.cells[nj] if nj is not None else []
            for c in range(max(len(ro), len(rn))):
                a = ro[c] if c < len(ro) else ""
                b = rn[c] if c < len(rn) else ""
                if norm_cmp(a) != norm_cmp(b):
                    diffs.append({"old_rc": (oi, c) if oi is not None else None, "new_rc": (nj, c) if nj is not None else None,
                                  "old": a, "new": b})
    return diffs


def _cell_box(t: TableBlock, rc) -> Optional[tuple]:
    if rc is None:
        return None
    r, c = rc
    try:
        return t.cell_boxes[r][c]
    except (IndexError, TypeError):
        return None


def _table_hunks(os_: Section, ns: Section, cap_map: dict, next_id, moved: bool) -> list[Hunk]:
    out = []
    if not os_.tables and not ns.tables:
        return out
    pairs, un_old, un_new = _align_tables(os_.tables, ns.tables, cap_map)
    for i, j in pairs:
        ot, nt = os_.tables[i], ns.tables[j]
        diffs = _table_cell_diff(ot, nt)
        if not diffs:
            continue
        out.append(_table_hunk_from(next_id(), "MODIFY", os_, ns, ot, nt, diffs, moved))
    for i in un_old:
        out.append(_table_hunk_from(next_id(), "DELETE", os_, ns, os_.tables[i], None, [], moved))
    for j in un_new:
        out.append(_table_hunk_from(next_id(), "ADD", os_, ns, None, ns.tables[j], [], moved))
    return out


def _table_hunk_from(hid, change_type, os_, ns, ot: Optional[TableBlock], nt: Optional[TableBlock], diffs: list, moved: bool) -> Hunk:
    label = (nt.label if nt and nt.label else (ot.label if ot and ot.label else "table")).title()
    if change_type == "MODIFY":
        old_text = "\n".join(f"[행{d['old_rc'][0] + 1} 열{d['old_rc'][1] + 1}] {d['old']}" for d in diffs if d["old_rc"] is not None and d["old"])
        new_text = "\n".join(f"[행{d['new_rc'][0] + 1} 열{d['new_rc'][1] + 1}] {d['new']}" for d in diffs if d["new_rc"] is not None and d["new"])
        
        # content that left a cell is shown by the other edition's box (table cells have no insertion band)
        old_boxes = [b for b in (_cell_box(ot, d["old_rc"]) for d in diffs if (d.get("old") or "").strip()) if b]
        new_boxes = [b for b in (_cell_box(nt, d["new_rc"]) for d in diffs if (d.get("new") or "").strip()) if b]
        old_anchors = [{"page": ot.page, "bbox": list(b)} for b in old_boxes] or ot.anchors()
        new_anchors = [{"page": nt.page, "bbox": list(b)} for b in new_boxes] or nt.anchors()
        editorial = all(_editorial_norm(d["old"]) == _editorial_norm(d["new"]) for d in diffs)
        fragment = all(_is_symbol_soup(d["old"] + " " + d["new"]) for d in diffs) and not editorial
        ops = [{"op": "replace", "old": d["old"][:200], "new": d["new"][:200]} for d in diffs[:DIFF_OPS_CAP]]
        ops_total = len(diffs)
    else:
        src = ot or nt
        old_text = src.flat_text() if ot else ""       # the whole table; the LLM payload marks any cut explicitly
        new_text = src.flat_text() if nt else ""
        old_anchors = ot.anchors() if ot else []
        new_anchors = nt.anchors() if nt else []
        editorial = False
        fragment = _is_symbol_soup(src.flat_text())
        ops = []
        ops_total = 0
    return Hunk(
        hunk_id=hid, change_type=change_type, unit="table", old_section=os_, new_section=ns, old_para=None, new_para=None,
        old_text=f"{label}\n{old_text}" if old_text else "", new_text=f"{label}\n{new_text}" if new_text else "",
        kind="fragment" if fragment else "table", editorial_only=editorial, renumber_only=False, similarity=0.0,
        moved_section=moved, old_changed_anchors=old_anchors, new_changed_anchors=new_anchors, diff_ops=ops, diff_ops_total=ops_total,
        verbal_form_only=False, fragment=fragment,
    )


def _make_hunk(hid, change_type, unit, os_, ns, op, np_, maps, moved, sim_=0.0) -> Hunk:
    renum, cap_map, eq_map = maps
    old_text = op.text if op else ""
    new_text = np_.text if np_ else ""
    kind = (np_.kind if np_ else op.kind) if (op or np_) else "section"
    # Editorial = equal after normalisation; the normalisation includes the Directives verbal-form rows, so a
    # rewording inside one provision row (shall <-> is required to) is editorial, a change of row is not.
    old_norm = _provision_norm(old_text) if (op and np_) else ""
    new_norm = _provision_norm(new_text) if (op and np_) else ""
    editorial = bool(op and np_) and old_norm == new_norm
    renumber = False
    if op and np_ and not editorial:
        old_norm = _provision_norm(_apply_renumber(old_text, renum, cap_map, eq_map))
        renumber = old_norm == new_norm
    ops = []
    if op and np_:
        ta, tb = tokens(_apply_renumber(old_text, renum, cap_map, eq_map)), tokens(new_text)
        sm = difflib.SequenceMatcher(None, ta, tb, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag != "equal":
                ops.append({"op": tag, "old": " ".join(ta[i1:i2])[:200], "new": " ".join(tb[j1:j2])[:200]})
    verbal = bool(op and np_) and not editorial and not renumber and _provision_type_changed_only(old_norm, new_norm)
    protected = kind in {"source", "caption", "note", "definition", "heading_text", "list"}
    fragment = (not protected) and unit == "paragraph" and (
        (op is not None and np_ is not None and _is_fragment(op) and _is_fragment(np_)) or
        (op is None and _is_fragment(np_)) or (np_ is None and _is_fragment(op)))
    return Hunk(
        hunk_id=hid, change_type=change_type, unit=unit, old_section=os_, new_section=ns, old_para=op, new_para=np_,
        old_text=old_text, new_text=new_text, kind="fragment" if fragment else kind,
        editorial_only=editorial, renumber_only=renumber, similarity=round(sim_, 3), moved_section=moved,
        old_changed_anchors=_changed_line_anchors(op, new_text) if op else [],
        new_changed_anchors=_changed_line_anchors(np_, old_text) if np_ else [],
        diff_ops=ops[:DIFF_OPS_CAP], diff_ops_total=len(ops), verbal_form_only=verbal, fragment=fragment,
        old_changed_words=_changed_word_anchors(op, new_text) if (op and np_) else [],
        new_changed_words=_changed_word_anchors(np_, old_text) if (op and np_) else [],
    )


SYSTEMATIC_MIN_HUNKS = 3
_PUNCT_ONLY_RE = re.compile(r"^[\W_]*$")


def mark_systematic_substitutions(hunks: list[Hunk]) -> list[dict]:
    """Document-derived rule. A token replacement that recurs in SYSTEMATIC_MIN_HUNKS or more different paragraphs
    of the document (may -> can, according to -> in accordance with, g F -> Fg) is a harmonisation applied
    throughout the new edition, not the correction of a local error: a local error is corrected once. Pairs that
    contain a digit never qualify (a value, a date or a reference number is always judged by the LLM), and a
    hunk whose diff list was cut at DIFF_OPS_CAP is not judged by it. A paragraph whose differences are all such
    pairs (plus punctuation) is classed SYSTEMATIC: it stays a candidate for items that name its region (a
    terminology item can be realised by exactly such a replacement) but is left out of the read-through for items
    that name no place, where it could only be mistaken for an 'error corrected'. Returns the pair table."""
    by_pair: dict = defaultdict(set)
    for h in hunks:
        if h.unit != "paragraph" or not (h.old_text and h.new_text):
            continue
        for op in h.diff_ops:
            if op["op"] == "replace" and not re.search(r"\d", op["old"] + op["new"]):
                by_pair[(op["old"], op["new"])].add(h.hunk_id)
    systematic = {p for p, ids in by_pair.items() if len(ids) >= SYSTEMATIC_MIN_HUNKS}
    for h in hunks:
        if (h.unit != "paragraph" or not (h.old_text and h.new_text) or not h.diff_ops or h.editorial_only or h.renumber_only
                or h.diff_ops_total > len(h.diff_ops)):
            continue
        pairs, only = [], True
        for op in h.diff_ops:
            if op["op"] == "replace" and (op["old"], op["new"]) in systematic:
                pairs.append(f"{op['old']} -> {op['new']} ({len(by_pair[(op['old'], op['new'])])} paragraphs)")
                continue
            if _PUNCT_ONLY_RE.match(op["old"]) and _PUNCT_ONLY_RE.match(op["new"]):
                continue
            only = False
        h.systematic_pairs = sorted(set(pairs))
        h.systematic_only = only and bool(pairs)
    table = sorted(({"old": p[0], "new": p[1], "hunks": len(ids)} for p, ids in by_pair.items() if p in systematic),
                   key=lambda r: (-r["hunks"], r["old"]))
    _log_event("SYSTEMATIC_SUBSTITUTIONS", pairs=len(table), hunks=sum(1 for h in hunks if h.systematic_only))
    return table


def _merge_fragment_hunks(hunks: list[Hunk], next_id) -> list[Hunk]:
    """Formula / table fragments of one section pair -> one hunk.

    Line by line, extracted formula text ("= + + x =") cannot be judged by anyone; per section the LLM sees the
    OLD and NEW formula text as a whole and the number of LLM batches stays bounded. Table hunks keep their own
    cell-level record. The merged hunk carries the anchors of all members (highlighting) and member_count.
    """
    groups: dict[tuple, list[Hunk]] = {}
    order: list[tuple] = []
    out: list[Hunk] = []
    for h in hunks:
        if h.fragment and h.unit == "paragraph" and not (h.editorial_only or h.renumber_only or h.systematic_only):
            key = (h.old_section.sid if h.old_section else "", h.new_section.sid if h.new_section else "")
            if key not in groups:
                groups[key] = []
                order.append(key)
            groups[key].append(h)
        else:
            out.append(h)
    for key in order:
        g = groups[key]
        if len(g) == 1:
            out.append(g[0])
            continue
        old_text = "\n".join(h.old_text for h in g if h.old_text)
        new_text = "\n".join(h.new_text for h in g if h.new_text)
        h0 = g[0]
        merged = Hunk(
            hunk_id=next_id(), change_type="MODIFY" if (old_text and new_text) else ("ADD" if new_text else "DELETE"),
            unit="fragments", old_section=h0.old_section, new_section=h0.new_section, old_para=None, new_para=None,
            old_text=old_text, new_text=new_text, kind="fragment", editorial_only=False, renumber_only=False,
            similarity=0.0, moved_section=h0.moved_section,
            old_changed_anchors=[a for h in g for a in h.old_changed_anchors],
            new_changed_anchors=[a for h in g for a in h.new_changed_anchors],
            diff_ops=[op for h in g for op in h.diff_ops][:DIFF_OPS_CAP], diff_ops_total=sum(h.diff_ops_total for h in g),
            verbal_form_only=False, fragment=True, member_count=len(g),
        )
        out.append(merged)
    return out


# ============================================================
# Stage 0/6 - document preparation entry point (CODE only, no LLM)
# ============================================================

def prepare_document(doc, side: str, lexicon_lines: Optional[list[list[Line]]] = None) -> dict:
    lines = extract_lines(doc, side)
    tables = extract_tables(doc, side)
    table_lines = mark_table_lines(lines, tables)
    hf = mark_running_headers_footers(lines, doc.page_count)
    toc = mark_toc_pages(lines)
    lang = mark_non_english_pages(lines)
    return {"lines": lines, "tables": tables, "table_lines": table_lines, "header_footer": hf, "toc": toc, "language": lang}


def analyse_pair_structure(old_doc, new_doc) -> dict:
    """Everything up to hunks, without any LLM call. Returns structures, alignment, hunks, metrics."""
    t0 = time.perf_counter()
    old_prep = prepare_document(old_doc, "OLD")
    new_prep = prepare_document(new_doc, "NEW")
    lexicon = build_lexicon([old_prep["lines"], new_prep["lines"]])
    old_struct = extract_structure(old_prep["lines"], "OLD", lexicon, old_prep["toc"]["entries"])
    new_struct = extract_structure(new_prep["lines"], "NEW", lexicon, new_prep["toc"]["entries"])
    attach_tables(old_struct["sections"], old_prep["tables"])
    attach_tables(new_struct["sections"], new_prep["tables"])
    alignment = align_sections(old_struct["sections"], new_struct["sections"])
    hunks = build_hunks(old_struct, new_struct, alignment)
    metrics = {
        "old": {**old_prep["header_footer"], "toc_pages": old_prep["toc"]["pages"], "toc_entries": len(old_prep["toc"]["entries"]),
                **old_prep["language"], **old_struct["stats"], "tables": len(old_prep["tables"]), "table_lines": old_prep["table_lines"],
                "toc_heading_recall": _toc_recall(old_prep["toc"]["entries"], old_struct["sections"])},
        "new": {**new_prep["header_footer"], "toc_pages": new_prep["toc"]["pages"], "toc_entries": len(new_prep["toc"]["entries"]),
                **new_prep["language"], **new_struct["stats"], "tables": len(new_prep["tables"]), "table_lines": new_prep["table_lines"],
                "toc_heading_recall": _toc_recall(new_prep["toc"]["entries"], new_struct["sections"])},
        "alignment": alignment["stats"],
        "hunks": {"total": len(hunks), **{k.lower(): v for k, v in Counter(h.rule_class for h in hunks).items()},
                  "systematic_pairs": alignment.get("systematic_pairs", [])},
        "elapsed_seconds": round(time.perf_counter() - t0, 2),
    }
    _log_event("STRUCTURE_METRICS", **metrics)
    return {"old": old_struct, "new": new_struct, "old_prep": old_prep, "new_prep": new_prep,
            "alignment": alignment, "hunks": hunks, "metrics": metrics}


def _toc_recall(toc_entries: list[dict], sections: list[Section]) -> Optional[float]:
    if not toc_entries:
        return None
    numbers = {s.number for s in sections}
    hit = 0
    for e in toc_entries:
        num = e["number"]
        if re.match(r"^Annex\s+[A-Z]$", num, re.I):
            num = "Annex " + num.split()[-1].upper()
        if num in numbers:
            hit += 1
    return round(hit / len(toc_entries), 3)


# ============================================================

# ============================================================

def page_text(doc, page_no: int) -> str:
    return clean(doc[page_no - 1].get_text("text"))


def _normalize_foreword_heading(line: str) -> str:
    value = unicodedata.normalize("NFKC", str(line or ""))
    for invisible in ("​", "‌", "‍", "⁠", "﻿"):
        value = value.replace(invisible, "")
    return re.sub(r"\s+", " ", clean(value)).strip().casefold()


def find_foreword_start(doc) -> int:
    candidates = []
    for page_no in range(1, doc.page_count + 1):
        for line in doc[page_no - 1].get_text("text").splitlines():
            normalized = _normalize_foreword_heading(line)
            if normalized == "foreword":
                _log_event("FOREWORD_EXACT_MATCH", page=page_no)
                return page_no
            if "foreword" in normalized and len(candidates) < 50:
                candidates.append({"page": page_no, "line": str(line)[:160]})
    _log_event("FOREWORD_NOT_FOUND", page_count=doc.page_count, candidates=candidates)
    raise RuntimeError(
        "PDF 텍스트에서 단독 FOREWORD 제목을 찾지 못했습니다. "
        f"FOREWORD 포함 후보 페이지={sorted({c['page'] for c in candidates})}."
    )


FOREWORD_SCHEMA = {
    "type": "object",
    "properties": {
        "has_revision_summary": {"type": "boolean"},
        "complete": {"type": "boolean"},
        "items": {"type": "array", "items": {"type": "object", "properties": {
            "marker": {"type": "string"}, "foreword_text": {"type": "string"},
            "action": {"type": "string", "enum": ["ADD", "DELETE", "MODIFY"]},
            "old_refs": {"type": "array", "items": {"type": "string"}},
            "new_refs": {"type": "array", "items": {"type": "string"}},
            "change_description_ko": {"type": "string"}, "confidence": {"type": "number"}},
            "required": ["marker", "foreword_text", "action", "old_refs", "new_refs", "change_description_ko", "confidence"]}},
    },
    "required": ["has_revision_summary", "complete", "items"],
}

FOREWORD_SYSTEM = r"""
You are a senior IEC standards revision analyst reading the FOREWORD of a NEW IEC edition.
The user supplies cumulative FOREWORD text from the FOREWORD heading through the current PDF page.
Identify ONLY the author-declared changes relative to the previous edition (the "significant technical changes"
list or equivalent wording). Do not invent clauses or changes. foreword_text must be a verbatim quote.
old_refs / new_refs may contain only references explicitly stated by the FOREWORD wording itself.
If the source has an item marker such as a), keep it in marker; otherwise return an empty marker.
complete=true only when the declared revision list has clearly ended in the cumulative text.
PAGE BREAKS: such lists often continue on the next page, and the last item on a page may end with a full stop
even though the list goes on (e.g. a)-c) on one page, d)-g) on the next). When the user marks the call as a
confirmation pass, the page after your previous "complete" judgement has been appended: re-read it, and if the
list continues there, include the additional items and keep complete=true only if the list has now ended.
Return JSON only.
"""


def _loose_norm(s: str) -> str:
    value = unicodedata.normalize("NFKC", str(s or "")).replace("­", "")
    return re.sub(r"[^0-9a-z가-힣]+", "", value.casefold())


def _quote_in_text(quote: str, text: str) -> bool:
    if norm(quote) in norm(text):
        return True
    lq, lt = _loose_norm(quote), _loose_norm(text)
    if lq and lq in lt:
        return True
    if len(lq) >= 40:
        match = difflib.SequenceMatcher(None, lq, lt, autojunk=False).find_longest_match(0, len(lq), 0, len(lt))
        if match.size >= int(len(lq) * 0.85):
            return True
    return False


def _validate_foreword_items(cumulative_text: str, items) -> list[dict]:
    out = []
    for idx, raw in enumerate(_as_list(items), start=1):
        if not isinstance(raw, dict):
            raise RuntimeError(f"FOREWORD 항목 {idx}: 항목이 JSON 객체가 아닙니다.")
        quote = clean(raw.get("foreword_text", ""))
        if not quote:
            raise RuntimeError(f"FOREWORD 항목 {idx}: 원문 인용이 비어 있습니다.")
        if not _quote_in_text(quote, cumulative_text):
            raise RuntimeError(f"FOREWORD 항목 {idx}: LLM 인용문이 실제 FOREWORD 텍스트와 일치하지 않습니다.")
        action = str(raw.get("action", "") or "").strip().upper()
        if action not in {"ADD", "DELETE", "MODIFY"}:
            raise RuntimeError(f"FOREWORD 항목 {idx}: 허용되지 않은 action={action}")
        out.append({
            "case_no": idx, "marker": clean(raw.get("marker", "")) or str(idx), "foreword_text": quote, "action": action,
            "old_refs": [clean(x) for x in _as_list(raw.get("old_refs")) if clean(x)],
            "new_refs": [clean(x) for x in _as_list(raw.get("new_refs")) if clean(x)],
            "change_description_ko": clean(raw.get("change_description_ko", "")),
            "confidence": max(0.0, min(1.0, _safe_float(raw.get("confidence"), 0.0))),
        })
    return out


def parse_foreword_sequentially(doc, base_url: str, model: str, progress=None) -> dict:
    """Page-by-page reading; the LLM decides when the declared list has ended.

    The only mechanical rule is that a "complete" judgement is confirmed once with the following page
    appended (a confirmation pass): the model, not a regex, decides whether the list continued there.
    """
    start = find_foreword_start(doc)
    if progress:
        progress(f"FOREWORD 시작 위치 p.{start}")
    cumulative_pages, cumulative_text = [], ""
    confirmed_through: Optional[int] = None   # page on which a previous "complete" was judged
    for page_no in range(start, doc.page_count + 1):
        if page_no - start >= FOREWORD_MAX_PAGES:
            raise RuntimeError(f"FOREWORD p.{start}부터 {FOREWORD_MAX_PAGES}페이지를 읽었지만 개정 선언의 종료를 판정하지 못했습니다.")
        cumulative_pages.append(page_no)
        cumulative_text = clean(cumulative_text + "\n\n" + page_text(doc, page_no))
        confirmation = confirmed_through is not None and page_no == confirmed_through + 1
        if progress:
            progress(f"LLM이 FOREWORD p.{start}~{page_no}를 읽고 개정 선언 종료 여부 판단" + (" (종료 확인용 다음 페이지)" if confirmation else ""))
        payload = {"foreword_start_page": start, "current_page": page_no, "cumulative_foreword_text": cumulative_text}
        if confirmation:
            payload["confirmation_pass"] = True
            payload["note"] = (f"On page {confirmed_through} you judged the declared list complete. Page {page_no} has now "
                               "been appended: check whether the list continues there before confirming.")
        out = ollama_chat_json(base_url, model, FOREWORD_SYSTEM, json.dumps(payload, ensure_ascii=False), FOREWORD_SCHEMA,
                               log_context={"phase": "FOREWORD", "current_page": page_no, "confirmation_pass": confirmation})
        if not out.get("complete"):
            confirmed_through = None
            continue
        items_raw = _as_list(out.get("items"))
        if not out.get("has_revision_summary") or not items_raw:
            _log_event("FOREWORD_PREMATURE_COMPLETE", page=page_no, item_count=len(items_raw))
            if page_no < doc.page_count:
                continue
            raise RuntimeError("LLM이 FOREWORD를 끝까지 읽었지만 이전 판 대비 공식 개정 선언을 확인하지 못했습니다.")
        items = _validate_foreword_items(cumulative_text, items_raw)
        if not confirmation and page_no < doc.page_count:
            # Ask once more with the next page appended; the LLM decides whether the list went on.
            confirmed_through = page_no
            _log_event("FOREWORD_COMPLETE_PENDING_CONFIRMATION", page=page_no, parsed_items=[it["marker"] for it in items])
            continue
        _log_event("FOREWORD_COMPLETE", page=page_no, items=[it["marker"] for it in items], confirmation_pass=confirmation)
        return {"found": True, "page": start, "end_page": page_no, "pages": list(cumulative_pages),
                "raw": cumulative_text, "items": items, "method": "sequential-text-llm"}
    raise RuntimeError("문서 끝까지 읽었지만 LLM이 FOREWORD 개정 선언의 종료를 판정하지 못했습니다.")




# ============================================================
# FOREWORD item -> document regions (default bucket for hunks)
# ============================================================

_REF_NUM_RE = re.compile(r"\b(?:Clause|Subclause|Annex|Table|Figure)?\s*((?:[A-Z]\b|\d+)(?:\.\d+)*)\b")


def _item_region_numbers(item: dict, sections: list[Section]) -> set[str]:
    """Section numbers (and all their descendants) that a FOREWORD item explicitly points to.

    Explicit references ("Clause 3", "3.2", "Annex B") are taken literally; a textual mention of a clause
    title ("terms and definitions") maps to sections whose title matches. Nothing else is inferred.
    """
    numbers: set[str] = set()
    all_numbers = {s.number for s in sections}
    refs = list(item.get("new_refs", [])) + list(item.get("old_refs", []))
    for ref in refs:
        ref = clean(ref)
        # Standard designations ("IEC 60060-2:2025", "ISO/IEC Guide 98-3") are not clause references.
        if re.search(r"\b(?:IEC|ISO|CISPR|IEEE|EN)\b", ref, re.I) or re.search(r"\d{4,}", ref):
            continue
        m = re.match(r"^\s*Annex\s+([A-Z])\b", ref, re.I)
        if m:
            numbers.add(f"Annex {m.group(1).upper()}")
            continue
        m = re.match(r"^\s*(?:Clause|Subclause|Sub-clause)?\s*((?:\d+)(?:\.\d+)*|[A-Z](?:\.\d+)+)\s*$", ref, re.I)
        if m and m.group(1) in all_numbers:
            numbers.add(m.group(1))
    text = norm_cmp(item.get("foreword_text", ""))
    # Only the explicit phrase names the terms clause; a bare "definitions" ("the definitions given there")
    # must not pull the whole terms clause into an item about another annex.
    if re.search(r"\bterms?\s+and\s+definitions\b", text):
        numbers |= _terms_clause_numbers(sections)
    return _expand_descendants(_most_specific(numbers), sections)


def _terms_clause_numbers(sections: list[Section]) -> set[str]:
    """The document's terms-and-definitions clause(s): top-level clauses with that title. Per-chapter
    'x.2 Terms and definitions' subsections (edition-1 style) are deliberately not included."""
    return {s.number for s in sections if s.level == 1 and s.kind == "clause" and TERMS_CLAUSE_TITLE_RE.search(s.title)}


def _is_ancestor(anc: str, num: str) -> bool:
    if anc == num:
        return False
    m = re.match(r"^Annex\s+([A-Z])$", anc)
    if m:
        return bool(re.match(rf"^{m.group(1)}(?:\.\d+)+$", num))
    return num.startswith(anc + ".")


def _most_specific(numbers: set[str]) -> set[str]:
    """Drop every reference that is an ancestor of another one in the set ("Annex G" + "G.8" -> "G.8")."""
    return {n for n in numbers if not any(_is_ancestor(n, other) for other in numbers)}


def _expand_descendants(numbers: set[str], sections: list[Section]) -> set[str]:
    expanded = set(numbers)
    for s in sections:
        node = s.parent
        while node is not None:
            if node.number in numbers:
                expanded.add(s.number)
                break
            node = node.parent
    return expanded


# ------------------------------------------------------------
# FOREWORD item -> search specification -> candidate hunks.
# The FOREWORD statement is the hypothesis; CODE collects the evidence that could realise it; the LLM
# only confirms whether a difference is an instance of the declared change. The LLM never decides on its
# own what is "meaningful" and then fits it to an item.
# ------------------------------------------------------------

SPEC_SCHEMA = {
    "type": "object",
    "properties": {"items": {"type": "array", "items": {"type": "object", "properties": {
        "marker": {"type": "string"},
        "target_regions": {"type": "array", "items": {"type": "string"}},
        "change_types": {"type": "array", "items": {"type": "string", "enum": ["ADD", "DELETE", "MODIFY", "MOVE"]}},
        "paragraph_kinds": {"type": "array", "items": {"type": "string", "enum": [
            "definition", "term", "note", "source", "body", "caption", "table", "equation", "heading_text", "any"]}},
        "text_patterns": {"type": "array", "items": {"type": "string"}},
        "moved_into_region": {"type": "boolean"},
        "whole_document": {"type": "boolean"},
        "evidence_rule_ko": {"type": "string", "maxLength": 300},
    }, "required": ["marker", "target_regions", "change_types", "paragraph_kinds", "text_patterns",
                    "moved_into_region", "whole_document", "evidence_rule_ko"]}}},
    "required": ["items"],
}

SPEC_SYSTEM = r"""
You translate each declared change in an IEC FOREWORD into a search specification over a structural diff of the
OLD and NEW editions. Use ONLY the FOREWORD wording; do not guess beyond it. One output per item, same order.
- target_regions: the clause / annex references exactly as the statement names them, one per entry
  ("Clause 3", "Annex B, Clause B.4", "Annex D", "Clause C.2", "Annex G, Clause G.8"). Use the token "TERMS_CLAUSE"
  when the statement refers to the terms and definitions clause by name. Empty when nothing is locatable.
- change_types: the structural operations the statement describes: added/new -> ADD; deleted/removed -> DELETE;
  modified/amended/replaced/clarified/corrected/simplified -> MODIFY; moved/relocated -> MOVE. Several allowed.
- paragraph_kinds: what the statement is about: definition/term/note/source for terminological entries, equation
  for formulas, table, caption for figures/tables, body for ordinary text, heading_text for titles, any when unspecified.
- text_patterns: literal strings the statement itself names that should appear in the changed text
  ("[SOURCE", "IEC 60000-1:2025", "test interval", "sampling interval", "Note 1"). Empty when it names none.
- moved_into_region: true when content is said to have been moved into the target region from elsewhere.
- whole_document: true when the statement cannot be located ("minor errors have been corrected").
- evidence_rule_ko: one Korean sentence: what a difference must show to count as an instance of this item.
change_types and paragraph_kinds guide the judge; they do not filter: every difference inside target_regions is examined.
Return JSON only.
"""


def _refs_from_text(tokens_: list[str]) -> set[str]:
    """Clause / annex references named in the tokens, as text ('3', 'G.8', 'Annex G', 'TERMS_CLAUSE')."""
    refs: set[str] = set()
    for tok in tokens_:
        tok = clean(str(tok))
        if not tok:
            continue
        if tok.upper() == "TERMS_CLAUSE":
            refs.add("TERMS_CLAUSE")
            continue
        if re.search(r"\b(?:IEC|ISO|CISPR|IEEE|EN)\b", tok, re.I) or re.search(r"\d{4,}", tok):
            continue   # standard designations are not clause references
        for m in re.finditer(r"\b(?:Clause|Subclause|Sub-clause)?\s*([A-Z](?:\.\d+)+|\d+(?:\.\d+)*)\b", tok):
            refs.add(m.group(1))
        m = re.search(r"\bAnnex\s+([A-Z])\b", tok, re.I)
        if m:
            refs.add(f"Annex {m.group(1).upper()}")
    return refs


def _resolve_region_tokens(tokens_: list[str], sections: list[Section]) -> set[str]:
    """Region tokens from the spec ('Clause 3', 'Annex G, Clause G.8', 'TERMS_CLAUSE') -> base section numbers
    (not yet expanded to descendants). Within one token the most specific reference wins."""
    numbers: set[str] = set()
    all_numbers = {s.number for s in sections}
    for tok in tokens_:
        tok = clean(str(tok))
        if not tok:
            continue
        if tok.upper() == "TERMS_CLAUSE":
            numbers |= _terms_clause_numbers(sections)
            continue
        hits: set[str] = set()
        for m in re.finditer(r"\b(?:Clause|Subclause|Sub-clause)?\s*([A-Z](?:\.\d+)+|\d+(?:\.\d+)*)\b", tok):
            if m.group(1) in all_numbers:
                hits.add(m.group(1))
        m = re.search(r"\bAnnex\s+([A-Z])\b", tok, re.I)
        if m and f"Annex {m.group(1).upper()}" in all_numbers:
            hits.add(f"Annex {m.group(1).upper()}")
        numbers |= _most_specific(hits)
    return numbers


def derive_item_specs(items: list[dict], base_url: str, model: str, old_secs: list[Section], new_secs: list[Section]) -> list[dict]:
    """LLM turns each FOREWORD statement into a spec; CODE resolves the regions to section numbers of both editions."""
    out = ollama_chat_json(base_url, model, SPEC_SYSTEM, json.dumps({
        "foreword_items": [{"marker": it["marker"], "action": it["action"], "foreword_text": it["foreword_text"],
                            "stated_refs": it.get("new_refs", []) + it.get("old_refs", [])} for it in items],
    }, ensure_ascii=False), SPEC_SCHEMA, num_predict=4096, log_context={"phase": "ITEM_SPECS", "items": len(items)})
    got = {str(x.get("marker", "")).strip(): x for x in _as_list(out.get("items")) if isinstance(x, dict)}
    specs = []
    for it in items:
        x = got.get(it["marker"], {})
        tokens_ = [str(t) for t in _as_list(x.get("target_regions"))] or list(it.get("new_refs", [])) + list(it.get("old_refs", []))
        # References are read as text first (spec tokens + the FOREWORD parse's literal refs), the most
        # specific ones are kept ("Annex G" + "G.9" -> G.9), and only then resolved per edition. A reference
        # that exists in one edition only (a new subclause) therefore yields an empty region on the other side
        # instead of falling back to the whole annex.
        text_refs = _refs_from_text(tokens_ + list(it.get("new_refs", [])) + list(it.get("old_refs", [])))
        wants_terms = "TERMS_CLAUSE" in text_refs or bool(re.search(r"\bterms?\s+and\s+definitions\b", norm_cmp(it.get("foreword_text", ""))))
        specific = _most_specific(text_refs - {"TERMS_CLAUSE"})

        def regions_for(sections):
            present = {s.number for s in sections}
            base = {r for r in specific if r in present}
            if wants_terms:
                base |= _terms_clause_numbers(sections)
            return _expand_descendants(base, sections)

        regions_new = regions_for(new_secs)
        regions_old = regions_for(old_secs)
        change_types = [str(c).upper() for c in _as_list(x.get("change_types")) if str(c).upper() in {"ADD", "DELETE", "MODIFY", "MOVE"}]
        kinds = [str(k) for k in _as_list(x.get("paragraph_kinds"))] or ["any"]
        spec = {
            "marker": it["marker"], "foreword_text": it["foreword_text"],
            "target_regions": tokens_, "regions_new": regions_new, "regions_old": regions_old,
            "change_types": change_types or ["ADD", "DELETE", "MODIFY", "MOVE"],
            "paragraph_kinds": kinds, "text_patterns": [str(p) for p in _as_list(x.get("text_patterns")) if str(p).strip()],
            "moved_into_region": bool(x.get("moved_into_region")),
            "whole_document": bool(x.get("whole_document")) or (not regions_new and not regions_old and not bool(x.get("moved_into_region"))),
            "evidence_rule_ko": clean(str(x.get("evidence_rule_ko", "") or "")),
        }
        specs.append(spec)
        _log_event("ITEM_SPEC", marker=it["marker"], target_regions=tokens_, regions_new=sorted(regions_new)[:12],
                   regions_old=sorted(regions_old)[:12], change_types=spec["change_types"], kinds=kinds,
                   patterns=spec["text_patterns"], moved=spec["moved_into_region"], whole_document=spec["whole_document"])
    return specs


def _cut(text: str, cap: int) -> str:
    """Payload text limited to `cap` characters with an explicit marker, so that the model knows what it did not see
    (and the log shows it)."""
    text = str(text or "")
    if len(text) <= cap:
        return text
    _log_event("PAYLOAD_TRUNCATED", chars=len(text), cap=cap)
    return text[:cap] + f" [TRUNCATED: {len(text) - cap} more characters not shown]"


def _fit_context(ctx: dict) -> dict:
    """Keep a section-context payload inside CONTEXT_TOTAL_CHARS: referenced sections are shortened first, then the
    two section texts, each with a TRUNCATED marker. Nothing is dropped without a trace."""
    def size():
        return len(json.dumps(ctx, ensure_ascii=False))
    guard = 0
    while size() > CONTEXT_TOTAL_CHARS and guard < 40:
        guard += 1
        refs = ctx.get("referenced_sections") or []
        longest_ref = max(refs, key=lambda e: len(e.get("old", "")) + len(e.get("new", "")), default=None)
        if longest_ref is not None and len(longest_ref.get("old", "")) + len(longest_ref.get("new", "")) > 1200:
            for side in ("old", "new"):
                longest_ref[side] = _cut(longest_ref[side], max(500, len(longest_ref[side]) // 2))
            continue
        key = max(("old_section_text", "new_section_text"), key=lambda k: len(ctx.get(k, "")))
        if len(ctx.get(key, "")) > 1500:
            ctx[key] = _cut(ctx[key], max(800, len(ctx[key]) // 2))
            continue
        break
    return ctx


def _hunk_text_has_pattern(h: Hunk, patterns: list[str]) -> bool:
    if not patterns:
        return True
    hay = norm_cmp(h.old_text + " \n " + h.new_text)
    return any(norm_cmp(p) and norm_cmp(p) in hay for p in patterns)


def select_candidates(hunks: list[Hunk], specs: list[dict]) -> dict:
    """CODE-side evidence collection per FOREWORD item.

    Every non-trivial difference inside the region the FOREWORD statement itself names (its clause / annex
    references, resolved to section numbers) is a candidate for that item; the LLM decides whether it is an
    instance. Rule-editorial and renumber hunks are never candidates (equal after the cited normalisations).
    Nothing else is filtered by code: the change types and paragraph kinds the LLM derived from the wording are
    passed to the judge as hints only - they are a reading of one sentence, not a fact about the document (a
    subclause the FOREWORD calls "amended" may in fact be new; a note deleted under a "modified" item is still its
    instance; a relocated section is a MOVE hunk that shows both locations). Items that name no place are handled
    by the full read-through (full_scan in classify_hunks).
    """
    for h in hunks:
        h.candidate_buckets = []
        h.default_bucket = ""
    for s in specs:
        if s["whole_document"]:
            s["full_scan"] = True
            continue
        for h in hunks:
            if h.rule_class in ("EDITORIAL", "RENUMBER"):
                continue
            new_in = bool(h.new_section and h.new_section.number in s["regions_new"])
            old_in = bool(h.old_section and h.old_section.number in s["regions_old"])
            if new_in or old_in:
                h.candidate_buckets.append(s["marker"])
    for h in hunks:
        h.candidate_buckets = list(dict.fromkeys(h.candidate_buckets))
        h.default_bucket = h.candidate_buckets[0] if len(h.candidate_buckets) == 1 else ""
    counts = Counter(m for h in hunks for m in h.candidate_buckets)
    counts["(none)"] = sum(1 for h in hunks if not h.candidate_buckets)
    _log_event("CANDIDATES_SELECTED", counts=dict(counts))
    return {s["marker"]: {"new": sorted(s["regions_new"]), "old": sorted(s["regions_old"])} for s in specs}


# ============================================================
# LLM classification of hunks
# ============================================================

# Two-stage cascade: a cheap verification for every candidate hunk, then a full Korean explanation per
# clause / entry. Output tokens dominate local-LLM latency, so the run time scales with the number of
# candidates the FOREWORD specs select, not with the number of textual differences.
TRIAGE_ITEM_SCHEMA = {
    "type": "object",
    "properties": {
        "hunk_id": {"type": "string"},
        "realizes_item": {"type": "string"},
        "meaning_changed": {"type": "boolean"},
        "reason_ko": {"type": "string", "maxLength": 160},
        "needs_context": {"type": "boolean"},
        "want_refs": {"type": "array", "items": {"type": "string"}, "maxItems": 6},
    },
    "required": ["hunk_id", "realizes_item", "meaning_changed", "reason_ko", "needs_context", "want_refs"],
}

EXPLAIN_ITEM_SCHEMA = {
    "type": "object",
    "properties": {
        "group_id": {"type": "string"},
        "title_ko": {"type": "string", "maxLength": 140},
        "old_meaning_ko": {"type": "string", "maxLength": 700},
        "new_meaning_ko": {"type": "string", "maxLength": 700},
        "technical_difference_ko": {"type": "string", "maxLength": 1000},
        "engineering_significance_ko": {"type": "string", "maxLength": 600},
        "confidence": {"type": "number"},
    },
    "required": ["group_id", "title_ko", "old_meaning_ko", "new_meaning_ko", "technical_difference_ko",
                 "engineering_significance_ko", "confidence"],
}


def triage_schema(markers: list[str]) -> dict:
    item_schema = json.loads(json.dumps(TRIAGE_ITEM_SCHEMA))
    item_schema["properties"]["realizes_item"] = {"type": "string", "enum": list(markers) + ["NONE"]}
    return {"type": "object", "properties": {"items": {"type": "array", "items": item_schema}}, "required": ["items"]}


EXPLAIN_SCHEMA = {"type": "object", "properties": {"items": {"type": "array", "items": EXPLAIN_ITEM_SCHEMA}}, "required": ["items"]}

TRIAGE_SYSTEM = r"""
You are a senior IEC standards engineer verifying evidence for the changes an IEC FOREWORD declares.

INPUT
- `foreword_items`: the NEW edition's FOREWORD list of declared changes (markers such as a), b), c)), each with the
  search specification derived from its wording (regions, change types, paragraph kinds, named text patterns) and an
  evidence rule stating what counts as an instance.
- `hunks`: differences found by deterministic structural comparison that fall inside the region named by at least
  one item (`candidate_foreword_items`) or - in a full read-through - every remaining difference of the document. Each gives the OLD and NEW text of one aligned paragraph, table or whole
  section, its location, the token-level diff operations and whether the section was relocated.

YOUR JOB, for every hunk, in the given order, exactly one output per hunk_id:
1. realizes_item: the candidate marker whose declared change this difference is an actual instance of, judged
   strictly by the FOREWORD wording and the evidence rule - not by your own view of what is important. Examples:
   an added "[SOURCE: ...]" line realizes an item declaring that sources were ascribed even though no technical
   meaning changed; a relocated definition realizes a "moved into Clause 3" item; a reworded definition realizes a
   "terms modified" item; a wording change unrelated to any candidate's wording is NONE. When a hunk fits two
   candidates, pick the one whose wording names the operation (moved / added / deleted / amended) that the hunk shows.
   The search specification's change_types and paragraph_kinds are hints, not filters: a hunk inside the region whose
   operation or paragraph kind differs from them can still be an instance (a subclause the FOREWORD calls "amended"
   may be new; a note deleted under a "modified" item is still its instance). Decide from the text.
   Hunks with rule_class FRAGMENT carry formula/table text as extracted from the PDF (see extraction_note): judge
   whether the formula/table content changed as declared; if the text is unreadable set needs_context=true.
   For an item that names no place (whole_document=true, e.g. "minor errors have been corrected") the program keeps
   your answer ONLY together with meaning_changed=true: answer that item when the OLD text is technically wrong and
   the NEW text corrects it - a wrong value, unit, symbol or index, a wrong equation, a wrong figure/table/clause/
   standard number, a wrong or missing word that changes what is required, measured or computed, a contradiction
   between two places - and say in reason_ko what was wrong. Everything else is NONE for such an item: rewording and
   synonyms ("according to" -> "in accordance with", "standard" -> "document"), grammar, spelling of ordinary words,
   capitalisation, punctuation, list markers, note numbering, abbreviation style, a sentence moved, and one
   non-mandatory verbal form replaced by another (may <-> can). A replacement listed under
   `systematic_substitutions` recurs across the whole document: it is a harmonisation of the edition, never a local
   error. A change that narrows or widens a requirement, deletes a condition or alters a value without the OLD text
   being wrong is a technical change, not an error correction: NONE unless another item declares it.
   An item's evidence is bounded by the operation its sentence names, and the program enforces it: "moved into" is
   realised only by the relocation itself (the MOVE of the section and the new container headings created for it);
   "added" only by additions (a new section, paragraph, note, or text inserted into a paragraph); "deleted" only by
   deletions; "amended / modified / clarified / replaced / simplified" by any difference in the named place. A
   reworded definition inside a relocated entry is NOT the relocation; a formula whose symbols were re-set is NOT a
   deletion or an addition: judge such a difference against the other candidate items or answer NONE.
   FULL READ-THROUGH: when every hunk in the batch lists the same single candidate, you are reading all remaining
   differences of the document for that one item; most of them will be NONE - do not force matches.
2. meaning_changed: true only if the technical content changed - what is required, recommended or permitted
   (shall / should / may), a definition, a value, a limit, a unit, a symbol or index, a formula, a procedure step or
   condition, the scope, or the target of a reference (clause, figure, table, standard number); a corrected wrong
   number or reference counts as changed. False for wording, grammar, format, note style, abbreviation style,
   renumbering that follows relocation, list markers, a reworded verbal form inside one provision type ("shall" ->
   "is required to") and a change between the non-mandatory forms (may <-> can). A note turned into body text or
   the reverse changes the status of its content (Directives Part 2: notes carry no requirements): true.
3. reason_ko: one short Korean sentence: what the difference is and why it does / does not realize the item.
4. needs_context: true only when the hunk text alone is insufficient to judge (a fragment, an unknown reference
   target, a list item without its lead-in). You will then receive the whole section pair.
5. want_refs: when the judgement depends on text the hunk only refers to (e.g. "see 5.3.2", "Figure 10",
   "Table 3", "Annex D", "Equation (G.4)"), list those references exactly as written and set needs_context=true;
   the program will fetch them from both editions for the next call. Empty list otherwise.
Use only the supplied text. Never invent clauses, values or consequences. Return JSON only.
"""

TRIAGE_CONTEXT_SYSTEM = TRIAGE_SYSTEM + r"""
This call supplies the FULL aligned OLD and NEW section text as context for ONE hunk that could not be judged alone,
plus the text of any clauses / figures / tables you asked for in want_refs (`referenced_sections`).
Judge that hunk only; needs_context must now be false and want_refs empty.
"""

EXPLAIN_SYSTEM = r"""
You are a senior IEC standards engineer. Each change below is one clause or terminological entry of the NEW edition
(with its OLD counterpart) together with ALL the differences in it that were confirmed as instances of one declared
FOREWORD item. Some instances change technical meaning; others realise the declaration without changing meaning
(a source ascribed, a definition relocated, a clause renumbered) - describe those as what they are, do not inflate them.
For every change, in the given order, write ONE coherent Korean analysis that an engineer reviewing the revision needs,
covering all listed differences together:
- title_ko: short title naming the clause/term and what was done;
- old_meaning_ko / new_meaning_ko: what the OLD and NEW text technically require, define or state;
- technical_difference_ko: the precise differences, quoting key terms, symbols and values exactly; number them when
  several exist; state explicitly when a difference is editorial or structural rather than technical;
- engineering_significance_ko: only consequences the text itself supports; say "없음" when none are stated;
- confidence 0..1.
Preserve IEC terminology, normative language, symbols, equations and units. Use only the supplied text.
Write plain text only: no LaTeX, no Markdown, no $...$ or backslash commands. Write symbols as Unicode characters
(κ, Δ, ×, ±, ², √) and subscripts as plain letters (F_Rog, I_rms, U_mes). Return JSON only.
"""


def _batches(hunks: list[Hunk], max_hunks: int, max_chars: int) -> list[list[Hunk]]:
    out, cur, size = [], [], 0
    for h in hunks:
        cost = len(h.old_text) + len(h.new_text) + 300
        if cur and (len(cur) >= max_hunks or size + cost > max_chars):
            out.append(cur)
            cur, size = [], 0
        cur.append(h)
        size += cost
    if cur:
        out.append(cur)
    return out


TRIAGE_BATCH_MAX_HUNKS = 20
TRIAGE_BATCH_CHARS = 14000
EXPLAIN_BATCH_MAX_GROUPS = 6
EXPLAIN_BATCH_CHARS = 11000
# Concurrent requests to Ollama. The server serialises them when OLLAMA_NUM_PARALLEL is 1, so this is never
# harmful; with two GPUs / parallel slots it roughly halves the triage time.
LLM_WORKERS = 2

def _run_batches(label: str, batches: list, worker, progress=None) -> list:
    """Run LLM batches with a small thread pool; results come back in batch order.

    A batch that fails on the transport level is retried once sequentially after the pool has drained
    (the server may have dropped a connection under parallel load); other failures propagate.
    """
    from concurrent.futures import ThreadPoolExecutor
    out = [None] * len(batches)
    failed: dict[int, Exception] = {}
    done = 0
    lock = threading.Lock()

    def job(idx):
        nonlocal done
        try:
            res = worker(idx, batches[idx])
        except OllamaTransportError as e:
            with lock:
                failed[idx] = e
            res = None
        with lock:
            done += 1
            if progress:
                progress(f"{label} {done}/{len(batches)}")
        return idx, res

    workers = max(1, min(LLM_WORKERS, len(batches)))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for idx, res in ex.map(job, range(len(batches))):
            out[idx] = res
    for idx, err in sorted(failed.items()):
        _log_event("BATCH_TRANSPORT_RETRY", label=label, batch=idx + 1, error=str(err)[:300])
        if progress:
            progress(f"{label} 배치 {idx + 1} 연결 오류 후 순차 재시도")
        time.sleep(5)
        out[idx] = worker(idx, batches[idx])
    return out


def _triage_batch(base_url, model, items_payload, t_schema, batch: list[Hunk], markers, log_context, open_markers=(), op_types=None) -> dict:
    out = ollama_chat_json(base_url, model, TRIAGE_SYSTEM, json.dumps({
        "foreword_items": items_payload, "hunks": [h.to_payload() for h in batch]}, ensure_ascii=False),
        t_schema, num_predict=DEFAULT_NUM_PREDICT, log_context=log_context)
    got = {str(x.get("hunk_id")): x for x in _as_list(out.get("items")) if isinstance(x, dict)}
    missing = [h.hunk_id for h in batch if h.hunk_id not in got]
    if missing:
        _log_event("TRIAGE_MISSING_ITEMS", context=log_context, missing=missing[:20], count=len(missing))
    res = {}
    for h in batch:
        x = got.get(h.hunk_id)
        if x is None:
            # Missing answer: keep the hunk visible under its single candidate (if any) and flag it.
            res[h.hunk_id] = {"hunk_id": h.hunk_id, "meaning_changed": True, "foreword_item": h.default_bucket or "NONE",
                              "reason_ko": "LLM 응답 누락 - 확인 필요", "needs_context": False, "llm_missing": True}
        else:
            res[h.hunk_id] = _normalise_triage(x, h, markers, open_markers, op_types)
    return res


def classify_hunks(hunks: list[Hunk], foreword_items: list[dict], specs: list[dict], base_url: str, model: str,
                   progress=None, cross_check: bool = False, old_secs: Optional[list] = None, new_secs: Optional[list] = None) -> dict:
    """Two-stage LLM verification of the candidate hunks selected by the FOREWORD specifications.

    Stage 1 asks, for every candidate hunk, which candidate item it realizes (or NONE); technical meaning change is
    recorded as information only. Optionally a second pass with a different batch composition is run and
    disagreements go to the section-context pass (self-consistency check).
    Stage 2 explains the confirmed instances, grouped per clause / terminological entry.
    Hunks that no specification selects are never sent to the LLM.
    """
    markers = [it["marker"] for it in foreword_items]
    open_markers = [s["marker"] for s in specs if s.get("whole_document")]   # items that name no place may be realised anywhere
    # Operation bound per item from the verbs of its FOREWORD sentence (search spec change_types). An item whose
    # sentence says amended / modified is unbounded (an "amended" subclause may in fact be new, 2.17).
    op_types = {s["marker"]: set(s.get("change_types") or []) for s in specs
                if s.get("change_types") and "MODIFY" not in s.get("change_types") and not s.get("whole_document")}
    t_schema = triage_schema(markers)
    spec_by_marker = {s["marker"]: s for s in specs}
    items_payload = []
    for it in foreword_items:
        s = spec_by_marker.get(it["marker"], {})
        items_payload.append({
            "marker": it["marker"], "action": it["action"], "foreword_text": it["foreword_text"],
            "description_ko": it.get("change_description_ko", ""),
            "search_spec": {"target_regions": s.get("target_regions", []), "change_types": s.get("change_types", []),
                            "paragraph_kinds": s.get("paragraph_kinds", []), "text_patterns": s.get("text_patterns", []),
                            "moved_into_region": s.get("moved_into_region", False), "whole_document": s.get("whole_document", False)},
            "evidence_rule_ko": s.get("evidence_rule_ko", ""),
        })
    to_llm = [h for h in hunks if h.candidate_buckets]
    to_llm.sort(key=lambda h: (0 if h.default_bucket else 1, (h.new_section or h.old_section).page_range()[0]))
    results: dict[str, dict] = {}

    # ---- Stage 1: verification (parallel batches) ----
    batches = _batches(to_llm, TRIAGE_BATCH_MAX_HUNKS, TRIAGE_BATCH_CHARS)
    total = len(batches)
    outs = _run_batches("LLM 1차 선별", batches,
                        lambda bi, b: _triage_batch(base_url, model, items_payload, t_schema, b, markers,
                                                    {"phase": "TRIAGE", "batch": bi + 1, "of": total, "hunks": len(b)}, open_markers, op_types),
                        progress)
    for res in outs:
        results.update(res)

    # ---- Stage 1a (optional): second triage with shuffled batch composition; disagreements need context ----
    disagreements = 0
    if cross_check:
        import random
        rng = random.Random(11)
        shuffled = list(to_llm)
        rng.shuffle(shuffled)
        batches2 = _batches(shuffled, TRIAGE_BATCH_MAX_HUNKS, TRIAGE_BATCH_CHARS)
        outs2 = _run_batches("LLM 1차 교차 검증", batches2,
                             lambda bi, b: _triage_batch(base_url, model, items_payload, t_schema, b, markers,
                                                         {"phase": "TRIAGE_CROSS", "batch": bi + 1, "of": len(batches2), "hunks": len(b)}, open_markers, op_types),
                             progress)
        second: dict[str, dict] = {}
        for res in outs2:
            second.update(res)
        for h in to_llm:
            a, b = results.get(h.hunk_id, {}), second.get(h.hunk_id, {})
            if a.get("foreword_item") != b.get("foreword_item"):
                a["needs_context"] = True
                a["cross_disagreement"] = {"first": a.get("foreword_item"), "second": b.get("foreword_item")}
                disagreements += 1
        _log_event("TRIAGE_CROSS_CHECK", disagreements=disagreements, hunks=len(to_llm))

    # ---- Stage 1b: section-context re-judgement for hunks the model could not judge alone (bounded) ----
    need = [h for h in to_llm if results.get(h.hunk_id, {}).get("needs_context")]
    need.sort(key=lambda h: 0 if h.default_bucket else 1)
    # Every hunk the model could not judge alone gets its section context - no cap: a cap would leave the rest
    # judged without the context the model asked for (only the run time grows).
    skipped_context = 0
    _log_event("TRIAGE_NEEDS_CONTEXT", count=len(need))

    def context_job(ci, h):
        wanted = results.get(h.hunk_id, {}).get("want_refs") or []
        excl = results.get(h.hunk_id, {}).get("exclude") or []
        pl = h.to_payload(max_chars=CONTEXT_HUNK_CHARS)
        if excl:
            pl["candidate_foreword_items"] = [m for m in pl["candidate_foreword_items"] if m not in excl]
            if pl.get("default_foreword_item") in excl:
                pl["default_foreword_item"] = ""
            pl["note"] = (f"Item(s) {', '.join(excl)} are bounded by the operation their sentence names, and this difference is not "
                          "that operation. Judge it against the remaining candidate items or answer NONE.")
        ctx = _fit_context({
            "foreword_items": items_payload, "hunks": [pl],
            "old_section_text": _cut(h.old_section.number + " " + (h.old_section.term or h.old_section.title) + "\n" + h.old_section.body_text(), CONTEXT_SECTION_CHARS) if h.old_section else "",
            "new_section_text": _cut(h.new_section.number + " " + (h.new_section.term or h.new_section.title) + "\n" + h.new_section.body_text(), CONTEXT_SECTION_CHARS) if h.new_section else "",
            "referenced_sections": _referenced_sections_text(wanted, old_secs or [], new_secs or []) if wanted else [],
        })
        if wanted:
            _log_event("TRIAGE_REFS_FETCHED", hunk=h.hunk_id, refs=wanted,
                       found=[bool(e["old"] or e["new"]) for e in ctx["referenced_sections"]])
        try:
            out = ollama_chat_json(base_url, model, TRIAGE_CONTEXT_SYSTEM, json.dumps(ctx, ensure_ascii=False), t_schema,
                                   num_predict=2048, log_context={"phase": "TRIAGE_CONTEXT", "hunk": h.hunk_id})
            got = [x for x in _as_list(out.get("items")) if isinstance(x, dict)]
            if got:
                r = _normalise_triage(got[0], h, markers, open_markers, op_types)
                r["needs_context"] = False
                r["context_pass"] = True
                if excl and r.get("foreword_item") in excl:
                    r["foreword_item"] = r["realizes_item"] = "NONE"
                    r["dropped_op"] = excl[0]
                return r
        except RuntimeError as e:
            _log_event("TRIAGE_CONTEXT_ERROR", hunk=h.hunk_id, error=str(e)[:300])
        return None

    ctx_outs = _run_batches("LLM 맥락 재판정", need, lambda ci, h: context_job(ci, h), progress)
    for h, r in zip(need, ctx_outs):
        if r is not None:
            prev = results[h.hunk_id]
            if prev.get("cross_disagreement"):
                r["cross_disagreement"] = prev["cross_disagreement"]
            results[h.hunk_id] = r

    # ---- Stage 1c: last resort - read EVERY remaining difference for items that cannot be located ----
    # Applies to items whose FOREWORD statement names no place (whole_document) and to items whose targeted
    # candidates yielded no confirmed instance. The LLM reads every difference of content, verbal-form and
    # fragment class that is not already confirmed for another item (a hunk has one explanation slot, and the
    # targeted pass offered it every item) and picks the instances itself; no rule pre-selects them.
    confirmed_ids = {hid for hid, r in results.items() if r.get("foreword_item") in markers}
    full_scan_markers = [s["marker"] for s in specs if s.get("full_scan")]
    for s in specs:
        if not s.get("full_scan") and not any(results.get(h.hunk_id, {}).get("foreword_item") == s["marker"] for h in to_llm):
            full_scan_markers.append(s["marker"])
            s["full_scan_reason"] = "no confirmed instance from targeted candidates"
    full_scan_stats = {}
    for marker in full_scan_markers:
        pool = [h for h in hunks if h.rule_class in ("CONTENT", "VERBAL_FORM", "FRAGMENT") and h.hunk_id not in confirmed_ids]
        if not pool:
            continue
        saved = {h.hunk_id: list(h.candidate_buckets) for h in pool}
        for h in pool:
            h.candidate_buckets = [marker]
        batches_fs = _batches(pool, TRIAGE_BATCH_MAX_HUNKS, TRIAGE_BATCH_CHARS)
        _log_event("FULL_SCAN_START", marker=marker, hunks=len(pool), batches=len(batches_fs),
                   reason=next((s.get("full_scan_reason", "whole_document") for s in specs if s["marker"] == marker), ""))
        outs_fs = _run_batches(f"LLM 전체 차이 통독 {marker}", batches_fs,
                               lambda bi, b: _triage_batch(base_url, model, items_payload, t_schema, b, markers,
                                                           {"phase": "FULL_SCAN", "marker": marker, "batch": bi + 1, "of": len(batches_fs), "hunks": len(b)}, open_markers, op_types),
                               progress)
        hits = 0
        for res in outs_fs:
            for hid, r in res.items():
                if r.get("foreword_item") == marker:
                    results[hid] = r
                    confirmed_ids.add(hid)
                    hits += 1
                elif hid not in results:
                    results[hid] = r      # scanned, judged NONE
        for h in pool:
            h.candidate_buckets = saved[h.hunk_id] if h.hunk_id not in confirmed_ids else [marker]
        full_scan_stats[marker] = {"scanned": len(pool), "batches": len(batches_fs), "confirmed": hits}
        _log_event("FULL_SCAN_DONE", marker=marker, **full_scan_stats[marker])
    if full_scan_markers:
        to_llm = [h for h in hunks if h.hunk_id in results]
        # context / reference requests raised during the full scan are honoured the same way
        need2 = [h for h in to_llm if results.get(h.hunk_id, {}).get("needs_context") and not results[h.hunk_id].get("context_pass")]
        ctx_outs2 = _run_batches("LLM 맥락 재판정(통독)", need2, lambda ci, h: context_job(ci, h), progress)
        for h, r in zip(need2, ctx_outs2):
            if r is not None:
                results[h.hunk_id] = r

    # ---- Stage 1d: identical differences at several places get one verdict ----
    # The same sentence changed the same way in parallel clauses (7.3.4, 8.3.4, 11.3.4 ...) must not be an instance
    # in one clause and NONE in another. Groups with mixed verdicts are re-asked once, all members together.
    same: dict = defaultdict(list)
    for h in to_llm:
        if h.unit == "paragraph" and h.old_text and h.new_text and h.hunk_id in results:
            same[(norm_cmp(h.old_text), norm_cmp(h.new_text))].append(h)
    mixed = [g for g in same.values() if len(g) > 1 and len({results[h.hunk_id].get("foreword_item") for h in g}) > 1]
    _log_event("CONSISTENCY_GROUPS", groups=len(mixed), hunks=sum(len(g) for g in mixed))

    def consistency_job(ci, g):
        payload = {"foreword_items": items_payload,
                   "note": (f"The following {len(g)} differences are the same text changed the same way at different places of the "
                            "document and were judged differently. Decide ONE answer that applies to all of them: the same "
                            "realizes_item and meaning_changed for every hunk_id (NONE is a valid common answer)."),
                   "hunks": [h.to_payload() for h in g]}
        try:
            out = ollama_chat_json(base_url, model, TRIAGE_SYSTEM, json.dumps(payload, ensure_ascii=False), t_schema,
                                   num_predict=DEFAULT_NUM_PREDICT, log_context={"phase": "TRIAGE_CONSISTENCY", "group": ci + 1, "hunks": len(g)})
            got = {str(x.get("hunk_id")): x for x in _as_list(out.get("items")) if isinstance(x, dict)}
            res_g = {}
            for h in g:
                x = got.get(h.hunk_id)
                if x is not None:
                    r = _normalise_triage(x, h, markers, open_markers, op_types)
                    r["needs_context"] = False
                    r["consistency_pass"] = True
                    res_g[h.hunk_id] = r
            return res_g
        except RuntimeError as e:
            _log_event("TRIAGE_CONSISTENCY_ERROR", group=ci + 1, error=str(e)[:300])
            return {}

    cons_outs = _run_batches("LLM 일관성 재판정", mixed, consistency_job, progress)
    for res_g in cons_outs:
        results.update(res_g or {})

    # ---- Stage 2: explanation per section pair for confirmed instances of declared items ----
    # Candidates the LLM rejected (NONE) and hunks no specification selected are discarded: the FOREWORD
    # defines what the reader must know.
    undeclared = [h for h in to_llm if results.get(h.hunk_id, {}).get("foreword_item") not in markers]
    changed = [h for h in to_llm if results.get(h.hunk_id, {}).get("foreword_item") in markers]
    groups: dict[tuple, list[Hunk]] = {}
    for h in changed:
        key = (results[h.hunk_id]["foreword_item"], h.old_section.sid if h.old_section else "", h.new_section.sid if h.new_section else "")
        groups.setdefault(key, []).append(h)
    group_list = [{"group_id": f"G{idx:04d}", "foreword_item": key[0], "hunks": hs} for idx, (key, hs) in enumerate(groups.items(), start=1)]
    for g in group_list:
        for h in g["hunks"]:
            results[h.hunk_id]["group_id"] = g["group_id"]

    def group_payload(g: dict, max_chars: int = EXPLAIN_DIFF_CHARS) -> dict:
        h0 = g["hunks"][0]
        return {
            "group_id": g["group_id"], "foreword_item": g["foreword_item"],
            "old_location": (h0.old_section.path() + (f" [{h0.old_section.term}]" if h0.old_section.term else "")) if h0.old_section else "",
            "new_location": (h0.new_section.path() + (f" [{h0.new_section.term}]" if h0.new_section.term else "")) if h0.new_section else "",
            "section_moved": any(h.moved_section for h in g["hunks"]),
            "differences": [{"hunk_id": h.hunk_id, "change_type": h.change_type, "kind": h.kind,
                             "old_text": _cut(h.old_text, max_chars), "new_text": _cut(h.new_text, max_chars),
                             "diff_ops": h.diff_ops, "triage_reason_ko": results[h.hunk_id].get("reason_ko", "")}
                            for h in g["hunks"]],
        }

    def group_cost(g):
        return sum(len(h.old_text) + len(h.new_text) + 300 for h in g["hunks"])

    ex_batches, cur, size = [], [], 0
    for g in group_list:
        c = group_cost(g)
        if cur and (len(cur) >= EXPLAIN_BATCH_MAX_GROUPS or size + c > EXPLAIN_BATCH_CHARS):
            ex_batches.append(cur)
            cur, size = [], 0
        cur.append(g)
        size += c
    if cur:
        ex_batches.append(cur)
    group_results: dict[str, dict] = {}

    def explain_job(bi, batch):
        try:
            out = ollama_chat_json(base_url, model, EXPLAIN_SYSTEM, json.dumps({
                "foreword_items": items_payload, "changes": [group_payload(g) for g in batch]}, ensure_ascii=False),
                EXPLAIN_SCHEMA, num_predict=DEFAULT_NUM_PREDICT,
                log_context={"phase": "EXPLAIN", "batch": bi + 1, "of": len(ex_batches), "groups": len(batch)})
            return {str(x.get("group_id")): x for x in _as_list(out.get("items")) if isinstance(x, dict)}
        except RuntimeError as e:
            _log_event("EXPLAIN_ERROR", batch=bi + 1, error=str(e)[:300])
            return {}

    ex_outs = _run_batches("LLM 2차 해설", ex_batches, explain_job, progress)
    for batch, got in zip(ex_batches, ex_outs):
        for g in batch:
            x = got.get(g["group_id"]) or {}
            reasons = " / ".join(r for r in (results[h.hunk_id].get("reason_ko", "") for h in g["hunks"]) if r)
            group_results[g["group_id"]] = {
                "group_id": g["group_id"], "foreword_item": g["foreword_item"], "hunk_ids": [h.hunk_id for h in g["hunks"]],
                "title_ko": clean(str(x.get("title_ko", "") or "")) or reasons or "(해설 없음)",
                "old_meaning_ko": clean(str(x.get("old_meaning_ko", "") or "")),
                "new_meaning_ko": clean(str(x.get("new_meaning_ko", "") or "")),
                "technical_difference_ko": clean(str(x.get("technical_difference_ko", "") or "")) or reasons,
                "engineering_significance_ko": clean(str(x.get("engineering_significance_ko", "") or "")),
                "confidence": max(0.0, min(1.0, _safe_float(x.get("confidence"), 0.0))),
                "explained": bool(x),
                "meaning_changed_any": any(results[h.hunk_id].get("meaning_changed") for h in g["hunks"]),
            }
    for h in to_llm:
        r = results[h.hunk_id]
        r.setdefault("title_ko", r.get("reason_ko", "") or "")
    not_candidates = sum(1 for h in hunks if not h.candidate_buckets and h.rule_class in ("CONTENT", "VERBAL_FORM", "FRAGMENT"))
    stats = {"candidate_hunks": len(to_llm), "non_candidate_hunks": not_candidates, "triage_batches": total,
             "cross_check": bool(cross_check), "cross_disagreements": disagreements,
             "context_passes": len(need), "context_skipped": skipped_context,
             "region_mismatch": sum(1 for r in results.values() if r.get("region_mismatch")),
             "dropped_no_meaning": sum(1 for r in results.values() if r.get("dropped_no_meaning")),
             "dropped_op": sum(1 for r in results.values() if r.get("dropped_op")),
             "consistency_groups": len(mixed), "consistency_hunks": sum(len(g) for g in mixed),
             "full_scan": full_scan_stats,
             "explain_groups": len(group_list), "explain_batches": len(ex_batches), "confirmed_hunks": len(changed),
             "rejected_candidates": len(undeclared), "undeclared_discarded": len(undeclared) + not_candidates,
             "by_item": dict(Counter(results[h.hunk_id]["foreword_item"] for h in changed))}
    _log_event("CLASSIFY_DONE", **stats)
    return {"results": results, "groups": group_results, "stats": stats}


def item_allows(h: Hunk, types: set) -> bool:
    """Does the hunk's operation fit the operations an item's sentence names? ADD / DELETE / MOVE as such; a MODIFY
    whose token diff is only insertions counts as an addition, only deletions as a deletion (text added to or removed
    from an existing paragraph); a relocation item also accepts the new container headings (ADD of a section). A
    diff list cut at DIFF_OPS_CAP is not judged (returns False, the LLM's answer is re-asked elsewhere)."""
    if not types or "MODIFY" in types:
        return True
    if h.change_type in types:
        return True
    if "MOVE" in types and h.change_type == "ADD" and h.unit == "section":
        return True
    if h.change_type == "MODIFY" and h.diff_ops and h.diff_ops_total <= len(h.diff_ops) and not h.fragment:
        # (a formula / figure fragment's token diff reflects extraction order, not an addition or a deletion)
        kinds = {op["op"] for op in h.diff_ops}
        if kinds <= {"insert"}:
            return "ADD" in types
        if kinds <= {"delete"}:
            return "DELETE" in types
    return False


def _normalise_triage(x: dict, h: Hunk, markers: list[str], open_markers=(), op_types=None) -> dict:
    """LLM answer -> {foreword_item (realized marker or NONE), meaning_changed (info), reason_ko, needs_context}.

    The model may choose any item whose region contains the hunk, or any item that names no place (open_markers).
    A marker outside that set is not silently replaced by another item: the hunk becomes NONE and the claim is kept
    in `region_mismatch`, so a wrong region resolution shows up in the log / JSON instead of being hidden.
    """
    item = str(x.get("realizes_item", x.get("foreword_item", "")) or "").strip()
    mismatch = dropped = not_move = ""
    if item not in markers:
        item = "NONE"
    elif item not in h.candidate_buckets and item not in open_markers:
        # Outside every candidate region (also for a hunk that is no item's candidate, judged in the read-through
        # context pass): the claim is kept as region_mismatch, the hunk stays NONE.
        mismatch, item = item, "NONE"
    elif item in open_markers and not bool(x.get("meaning_changed")):
        # An item that names no place ("minor errors corrected") is realised only by a difference that changes
        # technical content; a wording-only difference is editorial whatever the model answered. The reader needs
        # the meaning changes the FOREWORD declares, not every rewording of the edition.
        dropped, item = item, "NONE"
    elif op_types and item in op_types and not item_allows(h, op_types[item]):
        # The item's sentence names an operation (moved / added / deleted) and this difference is not that operation:
        # a reworded definition inside a relocated entry is not "moved into Clause 3", a re-set formula is not a
        # deletion. The hunk is re-judged against the other candidates (context pass with this item excluded) or
        # stays NONE.
        not_move, item = item, "NONE"
    want_refs = [clean(str(r)) for r in _as_list(x.get("want_refs")) if clean(str(r))][:6]
    out = {"hunk_id": h.hunk_id, "meaning_changed": bool(x.get("meaning_changed")), "foreword_item": item,
           "realizes_item": item, "reason_ko": clean(str(x.get("reason_ko", "") or "")),
           "needs_context": bool(x.get("needs_context")) or bool(want_refs), "want_refs": want_refs}
    if mismatch:
        out["region_mismatch"] = mismatch
    if dropped:
        out["dropped_no_meaning"] = dropped
    if not_move:
        out["dropped_op"] = not_move
        others = [m for m in h.candidate_buckets if m != not_move] + [m for m in open_markers if m != not_move]
        if others and not x.get("_context_pass"):
            out["needs_context"] = True
            out["exclude"] = [not_move]
    return out


def _referenced_sections_text(refs: list[str], old_secs: list[Section], new_secs: list[Section], max_chars: int = CONTEXT_REF_CHARS) -> list[dict]:
    """Fetch the text the LLM asked for ('5.3.2', 'Figure 10', 'Table 3', 'Annex D') from both editions.
    Clause references resolve to sections; figure/table references to the paragraphs that carry that caption."""
    out = []
    for ref in refs:
        entry = {"reference": ref, "old": "", "new": ""}
        m_cap = _CAPTION_LABEL_RE.search(ref)
        for side, secs in (("old", old_secs), ("new", new_secs)):
            if m_cap:
                label = f"{m_cap.group(1).lower()} {m_cap.group(2).lower()}"
                for s in secs:
                    hit = next((p for p in s.paragraphs if p.kind == "caption" and _CAPTION_LABEL_RE.match(p.text)
                                and f"{_CAPTION_LABEL_RE.match(p.text).group(1).lower()} {_CAPTION_LABEL_RE.match(p.text).group(2).lower()}" == label), None)
                    if hit:
                        entry[side] = _cut(s.path() + "\n" + hit.text, max_chars)
                        break
                continue
            numbers = _resolve_region_tokens([ref], secs)
            for s in secs:
                if s.number in numbers:
                    entry[side] = _cut(s.number + " " + (s.term or s.title) + "\n" + s.body_text(), max_chars)
                    break
        out.append(entry)
    return out


CASE_SUMMARY_SCHEMA = {
    "type": "object",
    "properties": {"title_ko": {"type": "string", "maxLength": 160}, "summary_ko": {"type": "string", "maxLength": 1600},
                   "severity": {"type": "string", "enum": ["HIGH", "MEDIUM", "LOW"]}, "confidence": {"type": "number"}},
    "required": ["title_ko", "summary_ko", "severity", "confidence"],
}

CASE_SUMMARY_SYSTEM = r"""
You are a senior IEC standards engineer. Write the case-level summary for ONE declared FOREWORD change item, using
only the list of confirmed technical changes assigned to it (titles and technical differences). Professional Korean,
concise, no invented content. Severity reflects engineering significance supported by the listed changes.
Plain text only: no LaTeX, no Markdown, no $...$; symbols as Unicode (κ, Δ, ×), subscripts as plain letters (F_Rog).
Return JSON only.
"""


def summarise_item(item: dict, changes: list[dict], base_url: str, model: str) -> dict:
    if not changes:
        return {"title_ko": clean(item.get("change_description_ko", "")) or item["foreword_text"],
                "summary_ko": "이 FOREWORD 항목에 배정된 내용 변경이 확인되지 않았습니다. 구조 diff 결과와 미선언 변경 섹션을 확인하세요.",
                "severity": "LOW", "confidence": 0.0}
    compact = [{"title": c["title_ko"], "difference": c["technical_difference_ko"], "location": c.get("new_location") or c.get("old_location")}
               for c in changes]          # every confirmed change, each with its full difference text
    out = ollama_chat_json(base_url, model, CASE_SUMMARY_SYSTEM, json.dumps({
        "foreword_item": {"marker": item["marker"], "foreword_text": item["foreword_text"], "action": item["action"]},
        "changes": compact, "change_count": len(changes),
    }, ensure_ascii=False), CASE_SUMMARY_SCHEMA, num_predict=4096, log_context={"phase": "ITEM_SUMMARY", "marker": item["marker"]})
    return {"title_ko": clean(str(out.get("title_ko", "") or "")), "summary_ko": clean(str(out.get("summary_ko", "") or "")),
            "severity": str(out.get("severity") or "MEDIUM").upper(),
            "confidence": max(0.0, min(1.0, _safe_float(out.get("confidence"), 0.0)))}


# ============================================================


# formulas and figures inside the clauses an item declares. Whole-document items declare no figures; a section that
# was added or deleted as a whole has nothing to compare. Everything else stays in the audit list.
VLM_MODEL = "qwen3-vl:32b-instruct"
VLM_CROP_ZOOM = 3.0          # rendering resolution of the crops handed to the model (display only, no judgement)
VLM_SCHEMA = {
    "type": "object",
    "properties": {
        "same": {"type": "string", "enum": ["yes", "no", "unsure"]},
        "changes": {"type": "array", "items": {"type": "object", "properties": {
            "kind": {"type": "string", "enum": ["symbol_renamed", "term_added", "term_removed", "structure_changed",
                                                "value_changed", "numbering_or_layout_only"]},
            "old": {"type": "string"}, "new": {"type": "string"}}, "required": ["kind", "old", "new"]}},
        "old_transcription": {"type": "string"}, "new_transcription": {"type": "string"},
        "confidence": {"type": "number"},
    },
    "required": ["same", "changes", "old_transcription", "new_transcription", "confidence"],
}
VLM_SYSTEM = r"""
You compare crops of ONE displayed formula, table or figure taken from two editions of an IEC standard. The first
images are from the OLD edition, the following ones from the NEW edition (the user message says how many of each).
1. Transcribe what you see in each edition as plain text, one line per equation, with a plain linear notation
   (e.g. kappa = I_p / (sqrt(2) * I_RMS); sums as sum_{i=1}^{N} ...). Transcribe only what is visible.
2. Compare the two transcriptions. Report ONLY differences that are visible in the images; never interpret meaning,
   correctness or intent. Allowed kinds: symbol_renamed (same structure, a symbol or name differs), term_added,
   term_removed, structure_changed (the expression is built differently), value_changed (a number differs),
   numbering_or_layout_only (equation number, spacing, font, line breaks).
3. same = "yes" only when the two editions show the same content apart from numbering_or_layout_only; "no" when at
   least one other kind of change is visible; "unsure" when a crop is unreadable or you cannot decide. Never guess.
Return JSON only.
"""


def _crop_png_b64(page, rect, zoom: float = VLM_CROP_ZOOM) -> str:
    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), clip=fitz.Rect(rect), alpha=False)
    return base64.b64encode(pix.tobytes("png")).decode("ascii")


def _vlm_crops(h: "Hunk", doc, side: str, graphics_cache: dict) -> list[dict]:
    """One crop per page: the union of the formula boxes (same rule as the highlight) of this fragment on that page."""
    anchors = h.old_changed_anchors if side == "old" else h.new_changed_anchors
    per_page: dict = defaultdict(list)
    for a in anchors:
        try:
            page = doc[int(a["page"]) - 1]
            r = fitz.Rect(a["bbox"]) & page.rect
        except Exception:
            continue
        if not r.is_empty:
            per_page[int(a["page"])].append(r)
    out = []
    for pno, rects in sorted(per_page.items()):
        page = doc[pno - 1]
        boxes = _formula_boxes(rects, _page_graphics(page, graphics_cache))
        u = boxes[0]
        for b in boxes[1:]:
            u = u | b
        out.append({"page": pno, "bbox": [round(v, 1) for v in (u.x0, u.y0, u.x1, u.y1)]})
    return out


def vlm_fragment_scope(hunks: list["Hunk"], specs: list[dict]) -> list["Hunk"]:
    region_items = {sp["marker"] for sp in specs if not sp.get("whole_document")}
    return [h for h in hunks if h.fragment and h.old_changed_anchors and h.new_changed_anchors
            and any(m in region_items for m in h.candidate_buckets)]


def vlm_compare_fragments(scope: list["Hunk"], old_doc, new_doc, base_url: str, vlm_model: str, stats: dict, progress=None) -> None:
    """Fills h.vlm for every fragment in scope. The answer is a fixed schema; the code only checks it for internal
    consistency (same=yes with substantive changes listed -> unsure) and never changes an item assignment with it."""
    graphics_cache: dict = {}
    for i, h in enumerate(scope, start=1):
        old_crops = _vlm_crops(h, old_doc, "old", graphics_cache)
        new_crops = _vlm_crops(h, new_doc, "new", graphics_cache)
        if not old_crops or not new_crops:
            continue
        if progress:
            progress(f"VLM 수식·그림 비교 {i}/{len(scope)}: {h.hunk_id} {(h.new_section or h.old_section).number if (h.new_section or h.old_section) else ''}")
        images = [_crop_png_b64(old_doc[c["page"] - 1], c["bbox"]) for c in old_crops] + \
                 [_crop_png_b64(new_doc[c["page"] - 1], c["bbox"]) for c in new_crops]
        user = json.dumps({"hunk_id": h.hunk_id, "old_images": len(old_crops), "new_images": len(new_crops),
                           "old_location": h.old_section.path() if h.old_section else "", "new_location": h.new_section.path() if h.new_section else "",
                           "foreword_items_in_scope": h.candidate_buckets}, ensure_ascii=False)
        try:
            res = ollama_vision_json(base_url, vlm_model, VLM_SYSTEM, user, images, VLM_SCHEMA,
                                     log_context={"phase": "VLM_FRAGMENT", "hunk_id": h.hunk_id})
        except RuntimeError as e:
            stats["errors"] += 1
            h.vlm = {"model": vlm_model, "error": str(e)[:300], "old_crops": old_crops, "new_crops": new_crops}
            continue
        same = res.get("same") if res.get("same") in ("yes", "no", "unsure") else "unsure"
        changes = [c for c in _as_list(res.get("changes")) if isinstance(c, dict) and c.get("kind")]
        substantive = [c for c in changes if c.get("kind") != "numbering_or_layout_only"]
        inconsistent = False
        if same == "yes" and substantive:
            same, inconsistent = "unsure", True
        if same == "no" and not substantive:
            same, inconsistent = "unsure", True
        h.vlm = {"model": vlm_model, "same": same, "changes": changes, "inconsistent": inconsistent,
                 "old_transcription": str(res.get("old_transcription") or ""), "new_transcription": str(res.get("new_transcription") or ""),
                 "confidence": res.get("confidence"), "old_crops": old_crops, "new_crops": new_crops,
                 "old_crops_png": [_crop_png_b64(old_doc[c["page"] - 1], c["bbox"], 1.6) for c in old_crops],
                 "new_crops_png": [_crop_png_b64(new_doc[c["page"] - 1], c["bbox"], 1.6) for c in new_crops]}
        stats["compared"] += 1
        if same == "unsure":
            stats["unsure"] += 1
        _log_event("VLM_FRAGMENT", hunk_id=h.hunk_id, same=same, changes=len(changes), inconsistent=inconsistent)


# ============================================================
# Result assembly
# ============================================================

def _hunk_record(h: Hunk, cls: Optional[dict]) -> dict:
    rec = {
        "hunk_id": h.hunk_id, "change_type": h.change_type, "unit": h.unit, "kind": h.kind, "rule_class": h.rule_class,
        "member_count": h.member_count,
        "old_location": h.old_section.path() if h.old_section else "", "new_location": h.new_section.path() if h.new_section else "",
        "old_title": (h.old_section.term or h.old_section.title) if h.old_section else "",
        "new_title": (h.new_section.term or h.new_section.title) if h.new_section else "",
        "old_text": h.old_text, "new_text": h.new_text, "similarity": h.similarity, "section_moved": h.moved_section,
        "old_anchors": h.old_changed_anchors, "new_anchors": h.new_changed_anchors,
        "old_pages": sorted({a["page"] for a in h.old_changed_anchors}), "new_pages": sorted({a["page"] for a in h.new_changed_anchors}),
        "diff_ops": h.diff_ops, "diff_ops_total": max(h.diff_ops_total, len(h.diff_ops)), "default_foreword_item": h.default_bucket,
        "old_words": h.old_changed_words, "new_words": h.new_changed_words, "systematic_pairs": h.systematic_pairs,
    }
    rec["candidate_foreword_items"] = list(h.candidate_buckets)
    if h.vlm:
        rec["vlm"] = h.vlm
    if cls:
        rec.update({k: cls.get(k) for k in ("meaning_changed", "foreword_item", "realizes_item", "title_ko", "reason_ko",
                                            "needs_context", "context_pass", "llm_missing", "group_id", "cross_disagreement", "region_mismatch",
                                            "dropped_no_meaning", "dropped_op", "consistency_pass") if k in cls})
    else:
        rec.update({"meaning_changed": False, "foreword_item": "NONE", "realizes_item": "NONE", "title_ko": _rule_label(h)})
    return rec


def _group_record(gid: str, g: dict, recs: list[dict]) -> dict:
    """Section-level change record: all meaning-changing hunks of one aligned section pair plus their explanation."""
    types = sorted({r["change_type"] for r in recs})
    first = recs[0]
    old_anchors = [a for r in recs for a in r.get("old_anchors", [])]
    new_anchors = [a for r in recs for a in r.get("new_anchors", [])]
    old_words = [w for r in recs for w in r.get("old_words", []) or []]
    new_words = [w for r in recs for w in r.get("new_words", []) or []]
    return {
        "group_id": gid, "hunk_id": gid, "foreword_item": g["foreword_item"], "hunk_ids": list(g["hunk_ids"]), "hunk_count": len(recs),
        "change_type": types[0] if len(types) == 1 else "MODIFY", "change_types": types,
        "kind": ", ".join(sorted({r["kind"] for r in recs})),
        "old_location": first.get("old_location", ""), "new_location": first.get("new_location", ""),
        "old_title": first.get("old_title", ""), "new_title": first.get("new_title", ""),
        "section_moved": any(r.get("section_moved") for r in recs),
        "old_anchors": old_anchors, "new_anchors": new_anchors, "old_words": old_words, "new_words": new_words,
        "old_pages": sorted({a["page"] for a in old_anchors}), "new_pages": sorted({a["page"] for a in new_anchors}),
        "old_gap_geometry": next((r["old_gap_geometry"] for r in recs if r.get("old_gap_geometry")), None),
        "new_gap_geometry": next((r["new_gap_geometry"] for r in recs if r.get("new_gap_geometry")), None),
        "hunks": recs,
        "meaning_changed": bool(g.get("meaning_changed_any")),
        "title_ko": g.get("title_ko", ""), "old_meaning_ko": g.get("old_meaning_ko", ""), "new_meaning_ko": g.get("new_meaning_ko", ""),
        "technical_difference_ko": g.get("technical_difference_ko", ""), "engineering_significance_ko": g.get("engineering_significance_ko", ""),
        "confidence": g.get("confidence", 0.0), "explained": g.get("explained", False),
    }


def _rule_label(h: Hunk) -> str:
    return {"EDITORIAL": "편집상 변경 (규칙 판정)", "RENUMBER": "번호 재부여만 변경 (규칙 판정)",
            "SYSTEMATIC": "전역 표현 통일 (규칙 판정: 문서 전체에서 되풀이되는 치환)",
            "FRAGMENT": "수식/표 조각 (LLM 판정 + 시각 확인)", "VERBAL_FORM": "조항 종류 변경 (Directives 서법 동사)"}.get(h.rule_class, "")


def fragment_groups(hunks: list[Hunk]) -> list[dict]:
    groups: dict[str, dict] = {}
    for h in hunks:
        if h.rule_class != "FRAGMENT":
            continue
        sec = h.new_section or h.old_section
        key = sec.number if sec else "?"
        g = groups.setdefault(key, {"section": key, "title": (sec.term or sec.title) if sec else "", "count": 0,
                                    "old_pages": set(), "new_pages": set(), "hunk_ids": []})
        g["count"] += h.member_count
        g["hunk_ids"].append(h.hunk_id)
        for a in h.old_changed_anchors:
            g["old_pages"].add(a["page"])
        for a in h.new_changed_anchors:
            g["new_pages"].add(a["page"])
        if not h.old_changed_anchors and h.old_section:
            g["old_pages"].add(h.old_section.page_range()[0])
        if not h.new_changed_anchors and h.new_section:
            g["new_pages"].add(h.new_section.page_range()[0])
    out = []
    for g in groups.values():
        out.append({**g, "old_pages": sorted(g["old_pages"]), "new_pages": sorted(g["new_pages"])})
    out.sort(key=lambda g: -g["count"])
    return out


def ghost_gap_for_add(h: Hunk, beads_by_pair: dict) -> Optional[dict]:
    """OLD insertion position for an added NEW paragraph: band under the OLD paragraph aligned to the
    nearest preceding NEW paragraph of the same section (same page only)."""
    if not (h.old_section and h.new_section and h.new_para):
        return None
    beads = beads_by_pair.get((h.old_section.sid, h.new_section.sid))
    if not beads:
        return None
    try:
        j = h.new_section.paragraphs.index(h.new_para)
    except ValueError:
        return None
    prev_old = None
    for oi, nj, _ in beads:
        if oi and nj and max(nj) < j:
            prev_old = oi[-1]
    if prev_old is None:
        return None
    anchors = h.old_section.paragraphs[prev_old].anchors()
    if not anchors:
        return None
    a = anchors[-1]
    x0, y0, x1, y1 = a["bbox"]
    return {"page": a["page"], "bbox": [x0, y1 + 1.0, x1, y1 + 5.0], "note": f"추가된 단락: '{clean(h.new_text)}'"}


def ghost_gap_for_delete(h: Hunk, beads_by_pair: dict) -> Optional[dict]:
    if not (h.old_section and h.new_section and h.old_para):
        return None
    beads = beads_by_pair.get((h.old_section.sid, h.new_section.sid))
    if not beads:
        return None
    try:
        i = h.old_section.paragraphs.index(h.old_para)
    except ValueError:
        return None
    prev_new = None
    for oi, nj, _ in beads:
        if oi and nj and max(oi) < i:
            prev_new = nj[-1]
    if prev_new is None:
        return None
    anchors = h.new_section.paragraphs[prev_new].anchors()
    if not anchors:
        return None
    a = anchors[-1]
    x0, y0, x1, y1 = a["bbox"]
    return {"page": a["page"], "bbox": [x0, y1 + 1.0, x1, y1 + 5.0], "note": f"삭제된 단락: '{clean(h.old_text)}'"}


def _section_lines(sec: Section) -> list:
    lines = list(sec.heading_lines) + [ln for p in sec.paragraphs for ln in p.lines]
    for child in sec.children:
        lines += _section_lines(child)
    return lines


def _band_after(lines: list) -> Optional[dict]:
    lines = [ln for ln in lines if not ln.removed]
    if not lines:
        return None
    last = max(lines, key=lambda ln: (ln.page, ln.bbox[3]))
    same_page = [ln for ln in lines if ln.page == last.page]
    x0 = min(ln.bbox[0] for ln in same_page)
    x1 = max(max(ln.bbox[2] for ln in same_page), x0 + 200.0)
    return {"page": last.page, "bbox": [x0, last.bbox[3] + 1.0, x1, last.bbox[3] + 5.0]}


def ghost_gap_for_section(h: Hunk, old_secs: list, new_secs: list, pairs: list) -> Optional[dict]:
    """Place of an added NEW section in the OLD edition (or of a deleted OLD section in the NEW one).

    Precise ("parent" basis): the nearest ancestor with a partner decides. Inside that ancestor's partner the band
    goes under the partner of the nearest preceding sibling (of the target, or of the new group the target belongs
    to) that has a partner there, else under the ancestor partner's own heading and text. G.9 under Annex G -> under
    OLD G.8; 3.11.6 inside the new group 3.11 under Clause 3 -> under OLD 3.7, the last subclause of OLD Clause 3
    (tree insertion under the matched ancestor, Chawathe et al. 1996).
    Estimated ("sibling" basis): no ancestor has a partner (OLD Annex C whose content became the whole NEW Annex
    C). The band then goes under the partner of the nearest preceding section in reading order and the report says
    so. None when nothing precedes with a partner."""
    if h.unit != "section" or h.change_type not in ("ADD", "DELETE"):
        return None
    if h.change_type == "ADD":
        secs, others, target = new_secs, old_secs, h.new_section
        partner = {p["new"]: p["old"] for p in pairs}
    else:
        secs, others, target = old_secs, new_secs, h.old_section
        partner = {p["old"]: p["new"] for p in pairs}
    index = {id(x): i for i, x in enumerate(secs)}
    idx = index.get(id(target))
    if idx is None:
        return None
    # Climb to the nearest ancestor that has a partner; `child` is the ancestor's child on the way to the target
    # (the target itself, or the new group it belongs to: 3.11.6 -> 3.11 under Clause 3 <-> OLD Clause 3).
    node, child = target.parent, target
    while node is not None and index.get(id(node)) not in partner:
        node, child = node.parent, node
    if node is not None:
        a_partner = others[partner[index[id(node)]]]
        best = None
        for sib in node.children:
            if sib is child:
                break
            sidx = index.get(id(sib))
            if sidx in partner and others[partner[sidx]].parent is a_partner:
                best = others[partner[sidx]]
        group = f"신설 묶음 {child.number} 전체가 " if child is not target else ""
        if best is not None:
            band = _band_after(_section_lines(best))
            note = f"{group}{node.number}의 짝 {a_partner.number} 안, 앞 절 {best.number} 뒤"
        else:
            band = _band_after(list(a_partner.heading_lines) + [ln for p in a_partner.paragraphs for ln in p.lines]) \
                or _band_after(_section_lines(a_partner))
            note = f"{group}{node.number}의 짝 {a_partner.number}의 첫 하위 절 자리"
        if band:
            band.update({"basis": "parent", "note": note})
            return band
    for k in range(idx - 1, -1, -1):
        if k not in partner:
            continue
        band = _band_after(_section_lines(others[partner[k]]))
        if band:
            band.update({"basis": "sibling",
                         "note": f"앞 절 {secs[k].number}의 짝 {others[partner[k]].number} 뒤로 추정 (상위 절 {target.parent.number if target.parent is not None else '—'}은 상대 판에 짝이 없음)"})
            return band
    return None


# ============================================================
# Highlighting
# ============================================================

def change_rgb(change_type: str) -> tuple:
    """Kept for compatibility; boxes are coloured per FOREWORD item since fix 8 (see item_rgb)."""
    return {"ADD": (0.10, 0.63, 0.35), "DELETE": (0.85, 0.20, 0.18), "MOVE": (0.55, 0.30, 0.80)}.get(change_type, (0.15, 0.38, 0.85))


# Tableau 10 categorical palette (Stone & Heer): ten hues chosen to stay distinguishable for category coding.
ITEM_PALETTE = [(0.12, 0.47, 0.71), (1.00, 0.50, 0.05), (0.17, 0.63, 0.17), (0.84, 0.15, 0.16), (0.58, 0.40, 0.74),
                (0.55, 0.34, 0.29), (0.89, 0.47, 0.76), (0.50, 0.50, 0.50), (0.74, 0.74, 0.13), (0.09, 0.75, 0.81)]

CHANGE_TYPE_KO = {"ADD": "추가", "DELETE": "삭제", "MODIFY": "수정", "MOVE": "이동"}
KIND_KO = {"body": "본문", "term": "용어", "definition": "정의", "note": "주석", "source": "출처", "caption": "캡션",
           "list": "목록", "equation": "수식", "heading_text": "제목", "table": "표", "fragment": "수식·표 조각",
           "fragments": "수식·표 조각 묶음", "section": "절 전체", "paragraph": "단락", "any": "제한 없음", "raw": "미분류"}
RULE_KO = {"EDITORIAL": "편집상(규칙 판정)", "RENUMBER": "재번호(규칙 판정)", "SYSTEMATIC": "전역 표현 통일(규칙 판정)", "VERBAL_FORM": "조항 종류 변경",
           "FRAGMENT": "수식·표 조각", "CONTENT": "내용 차이(LLM 판정: 어느 항목의 사례도 아님)"}
SEVERITY_KO = {"HIGH": "중요도 높음", "MEDIUM": "중요도 중간", "LOW": "중요도 낮음"}
ALIGN_METRIC_KO = {
    "old_sections": "구판 절 수", "new_sections": "신판 절 수",
    "stage_A": "A단계로 짝지은 절(번호와 제목이 같음)", "stage_B": "B단계로 짝지은 절(제목은 같고 번호만 다름)",
    "stage_C": "C단계로 짝지은 절(본문 유사도)", "stage_D": "D단계로 짝지은 절(본문 없는 상위 절: 번호 또는 하위 절의 짝으로)",
    "deleted_sections": "구판에만 있는 절", "added_sections": "신판에만 있는 절",
    "stage_C_threshold": "C단계 유사도 임계값(문서 쌍에서 보정)",
    "calibration_positive_n": "임계값 보정 표본: 확실한 짝 수", "calibration_negative_n": "임계값 보정 표본: 무작위 비(非)짝 수",
    "coverage_new": "신판 절 가운데 짝이 있는 비율",
    "paragraph_threshold": "단락 짝 유사도 임계값(보정값)", "paragraph_threshold_source": "단락 임계값 출처(valley = 유사도 분포의 골짜기)",
    "paragraph_valley": "유사도 분포의 골짜기 위치", "paragraph_otsu": "Otsu 분할값(참고)", "paragraph_otsu_eta": "Otsu 분리도(0~1)",
    "paragraph_chance_p90": "우연 일치 상한(무작위 짝 상위 10 %)", "paragraph_calibration_n": "단락 보정 표본 수",
    "paragraph_negative_n": "무작위 비(非)짝 표본 수",
}

_GREEK = {"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε", "varepsilon": "ε", "zeta": "ζ", "eta": "η",
          "theta": "θ", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π", "rho": "ρ", "sigma": "σ",
          "tau": "τ", "phi": "φ", "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω", "Delta": "Δ", "Gamma": "Γ",
          "Theta": "Θ", "Lambda": "Λ", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω"}
_MATH_SYMBOLS = {"times": "×", "cdot": "·", "pm": "±", "approx": "≈", "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥",
                 "neq": "≠", "ne": "≠", "infty": "∞", "sqrt": "√", "sum": "Σ", "int": "∫", "rightarrow": "→", "to": "→",
                 "leftarrow": "←", "propto": "∝", "partial": "∂", "deg": "°", "circ": "°", "ldots": "…", "cdots": "…"}


def _plain_math(s: str) -> str:
    """Flatten LaTeX the LLM may still write ($F_{Rog}$, \\Delta, \\text{...}) into plain Unicode text for display."""
    s = str(s or "")
    if "\\" not in s and "$" not in s:
        return s
    s = re.sub(r"\\(?:text|textrm|mathrm|mathit|mathbf|operatorname)\s*\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}", r"(\1)/(\2)", s)
    s = re.sub(r"\\sqrt\s*\{([^{}]*)\}", r"√(\1)", s)
    s = re.sub(r"\\(?:left|right|displaystyle|quad|qquad)\b", " ", s)
    s = re.sub(r"\\[,;!]", " ", s)
    s = re.sub(r"\\([A-Za-z]+)", lambda m: _GREEK.get(m.group(1)) or _MATH_SYMBOLS.get(m.group(1)) or m.group(1), s)
    s = s.replace("\\%", "%")
    s = re.sub(r"_\{([^{}]*)\}", r"_\1", s)
    s = re.sub(r"\^\{([^{}]*)\}", r"^\1", s)
    s = s.replace("$", "").replace("{", "").replace("}", "")
    return re.sub(r"[ \t]{2,}", " ", s)


# Glyph variants (phi symbol, lunate epsilon, ...) that common UI fonts lack: shown as the base letter.
_GLYPH_VARIANTS = str.maketrans({"ϕ": "φ", "ϵ": "ε", "ϑ": "θ", "ϱ": "ρ", "ϖ": "π", "µ": "μ"})


def _display_text(s: str) -> str:
    """Display form of PDF-extracted text: Symbol-font private-use characters -> Greek, glyph variants -> base letter."""
    return _map_symbol_pua(str(s or "")).translate(_GLYPH_VARIANTS)


def item_rgb(marker: str, markers: list) -> tuple:
    """Colour of a FOREWORD item: the box colour tells which declaration a change belongs to."""
    idx = markers.index(marker) if marker in markers else len(markers)
    return ITEM_PALETTE[idx % len(ITEM_PALETTE)]


def rgb_hex(rgb: tuple) -> str:
    return "#%02x%02x%02x" % tuple(int(round(v * 255)) for v in rgb)


def assign_change_labels(items: list) -> None:
    """'a)-12' = the 12th change record of item a) in the report; the same label is printed beside the PDF boxes."""
    for it in items:
        for i, c in enumerate(it.get("changes") or [], start=1):
            c["label"] = f"{it['marker']}-{i}"


def printed_page_numbers(lines: list) -> dict:
    """PDF page index -> page number printed on the page.

    Candidates are the header/footer-band lines that look like a bare number ('– 12 –', '16'); per page the one
    nearest the page edge is taken. Printed numbers run consecutively, so the offset (printed − index) shared by
    most pages is the document's offset: pages between the first and last page carrying it are numbered by it, and
    candidates with another offset (a table number or footnote mark that happens to sit in the band) are ignored.
    """
    best: dict = {}
    for ln in lines:
        if ln.removed not in ("header_footer", "page_number") or not _PAGE_NUMBER_RE.match(ln.text):
            continue
        edge = min(ln.y_ratio, 1.0 - ln.y_ratio)
        if ln.page not in best or edge < best[ln.page][0]:
            best[ln.page] = (edge, int(re.search(r"\d{1,4}", ln.text).group(0)))
    if not best:
        return {}
    offset, support = Counter(num - page for page, (_, num) in best.items()).most_common(1)[0]
    if support < 3:
        return {}
    body = [page for page, (_, num) in best.items() if num - page == offset]
    return {page: str(page + offset) for page in range(min(body), max(body) + 1)}


def _overlapping(a, b) -> bool:
    """Boxes that intersect or touch (nested formula pieces, a section box over its own paragraphs)."""
    return a.x1 >= b.x0 and b.x1 >= a.x0 and a.y1 >= b.y0 and b.y1 >= a.y0


def _merge_rects(rects: list) -> list:
    """Union of overlapping boxes of one change on one page: nested formula pieces become one box instead of a
    pile of overlapping ones. Boxes that do not touch (separate paragraphs) stay separate."""
    rs = [fitz.Rect(r) for r in rects]
    changed = True
    while changed:
        changed = False
        out: list = []
        for r in rs:
            for i, o in enumerate(out):
                if _overlapping(r, o):
                    out[i] = o | r
                    changed = True
                    break
            else:
                out.append(r)
        rs = out
    return rs


def _page_graphics(page, cache: dict) -> list:
    """Vector-drawing clusters (figures, formula bars) and raster images of a page. Must be read before any
    annotation is added to the page (annotation appearances would otherwise count as drawings)."""
    key = (id(page.parent), page.number)
    if key not in cache:
        cache[key] = _graphics_of_page(page)
    return cache[key]


def _page_text_left(page, cache: dict) -> float:
    key = (id(page.parent), page.number)
    if key not in cache:
        xs = [l["bbox"][0] for b in page.get_text("dict").get("blocks", []) if b.get("type") == 0
              for l in b.get("lines", []) if any(sp.get("text", "").strip() for sp in l.get("spans", []))]
        cache[key] = min(xs) if xs else 70.0
    return cache[key]


def _formula_boxes(rects: list, graphics: list) -> list:
    """One box per displayed formula or figure (fix 16 B). The fragment boxes of one change on one page are widened
    by every drawing cluster or image they intersect (fraction bars, radicals, a graph's grid) and then chained by
    vertical overlap: the pieces of one displayed formula share its vertical band, while the body text between two
    formulas is never a fragment and so keeps them apart. The PDF text block is not usable as the unit - the 2010
    PDF stores one symbol per block. Returns the union box of every chain; no size thresholds."""
    rs = []
    for r in rects:
        r = fitz.Rect(r)
        for g in graphics:
            # a drawing the fragment intersects (fraction bar, radical), or a figure within whose vertical span the
            # fragment lies (axis tick labels and axis titles stand beside the plot frame, not inside it)
            if g.intersects(r) or (g.y0 <= r.y0 and r.y1 <= g.y1):
                r = r | g
        rs.append(r)
    chains: list = []
    for r in rs:
        hit = [c for c in chains if c.y1 >= r.y0 and r.y1 >= c.y0]
        for c in hit:
            chains.remove(c)
            r = r | c
        chains.append(r)
    return chains


def _annot_rect(page, bbox, rgb, title: str, content: str, opacity: float = 0.16, width: float = 1.0, popup: bool = True) -> bool:
    try:
        rect = fitz.Rect(bbox)
    except Exception:
        return False
    if rect.is_empty or rect.is_infinite:
        return False
    rect &= page.rect
    if rect.is_empty:
        return False
    ann = page.add_rect_annot(rect)
    ann.set_colors(stroke=rgb, fill=rgb)
    ann.set_opacity(opacity)
    ann.set_border(width=width)
    ann.set_info(title=title, content=str(content or ""))
    if popup:
        try:   # a popup object makes the note openable in viewers that ignore bare /Contents (Chrome, Edge)
            pw = page.rect.width
            ann.set_popup(fitz.Rect(max(0.0, pw - 230.0), rect.y0, pw - 10.0, rect.y0 + 90.0))
        except Exception:
            pass
    ann.update()
    return True


def _place_label(page, rect, text: str, rgb, placed: list, text_left: float) -> bool:
    """Small label in the margin beside the first box of a change on the page; labels never overlap each other."""
    w = 4.2 * len(text) + 6.0
    h = 10.5
    x0 = text_left - w - 3.0 if text_left - w - 3.0 >= 2.0 else min(page.rect.width - w - 2.0, rect.x1 + 3.0)
    box = fitz.Rect(x0, rect.y0, x0 + w, rect.y0 + h)
    for _ in range(16):
        hit = next((q for q in placed if q.intersects(box)), None)
        if hit is None:
            break
        box = fitz.Rect(x0, hit.y1 + 1.0, x0 + w, hit.y1 + 1.0 + h)
    if box.y1 > page.rect.height - 2.0:
        box = fitz.Rect(x0, page.rect.height - h - 2.0, x0 + w, page.rect.height - 2.0)
    placed.append(box)
    try:
        a = page.add_freetext_annot(box, text, fontsize=7, fontname="helv", text_color=rgb, fill_color=(1, 1, 1), border_width=0.6)
        a.set_info(title=text, content=text)
        a.update()
        return True
    except Exception:
        return False


def _legend_font() -> dict:
    """A Korean-capable font for the legend page: the system's Malgun Gothic / Noto CJK when present, else MuPDF's
    built-in CJK face."""
    for cand in (r"C:\Windows\Fonts\malgun.ttf", "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
                 "/System/Library/Fonts/AppleSDGothicNeo.ttc"):
        if os.path.exists(cand):
            return {"fontname": "legendko", "fontfile": cand}
    return {"fontname": "korea"}


def _insert_fitting(page, rect, text: str, fontsize: float, font: dict) -> None:
    """insert_textbox writes nothing when the text overflows; shrink the type until it fits."""
    for fs in (fontsize, fontsize - 1, fontsize - 2, fontsize - 3):
        if page.insert_textbox(rect, text, fontsize=fs, **font) >= 0:
            return


def _append_legend(doc, items: list, markers: list, side: str) -> None:
    """Last page of each highlighted PDF: colour per item, what the label and the thin strip mean."""
    page = doc.new_page(width=595, height=842)
    font = _legend_font()
    _insert_fitting(page, fitz.Rect(50, 36, 545, 60), f"하이라이트 범례 ({side} 판) — IEC Revision Analyzer v7", 13, font)
    intro = ("상자 색 = FOREWORD에 선언된 변경 항목(아래 표). 상자 왼쪽 여백의 작은 라벨(예: a)-12) = HTML 보고서 1절의 변경 번호"
             "(항목 a)의 12번째 변경 기록). 가는 띠 = 추가(삭제)된 내용이 이 판에서 들어갈(있던) 자리. "
             "상자 안의 진한 채움 = 실제로 바뀐 단어. 상자를 클릭하면 변경 요약 메모가 열립니다. 보고서 버튼의 p.N은 PDF 쪽 번호이고, "
             "괄호 안 '인쇄 N'은 지면에 찍힌 쪽 번호입니다. 변경 하나만 따로 보려면 HTML 보고서의 OLD/NEW 버튼을 쓰세요(그 변경의 상자만 색으로 표시).")
    _insert_fitting(page, fitz.Rect(50, 66, 545, 140), intro, 9.5, font)
    y = 150.0
    for it in items:
        rgb = item_rgb(it["marker"], markers)
        title_txt = _display_text(_plain_math(clean(it.get('title_ko', ''))))
        fore_txt = _display_text(clean(it.get('foreword_text', '')))
        body = f"{it['marker']} {title_txt}\n{fore_txt}"
        # box height from the text itself (about 45 Korean or 90 Latin characters per 465 pt line at 9 pt)
        height = (math.ceil(len(title_txt) / 45) + math.ceil(len(fore_txt) / 90) + 1) * 12.0 + 10.0
        if y + height > 800:
            page = doc.new_page(width=595, height=842)
            y = 50.0
        sh = page.new_shape()
        sh.draw_rect(fitz.Rect(50, y, 72, y + 14))
        sh.finish(color=rgb, fill=rgb, fill_opacity=0.25, width=1)
        sh.commit()
        _insert_fitting(page, fitz.Rect(80, y - 3, 545, y + height), body, 9, font)
        y += height + 6.0


def _draw_change(doc, side: str, ch: dict, rgb, label: str, title: str, note: str, caches: dict, counts: dict) -> int:
    per_page: dict = defaultdict(list)
    cell_boxes: dict = defaultdict(list)          
    frag_anchors: dict = defaultdict(list)        # page -> [(anchor, rect)] of formula/table/figure fragments
    for h in (ch.get("hunks") or [ch]):
        fragment = h.get("kind") == "fragment" or h.get("unit") == "fragments"
        for a in h.get(f"{side}_anchors", []) or []:
            try:
                page = doc[int(a["page"]) - 1]
                r = fitz.Rect(a["bbox"]) & page.rect
            except Exception:
                continue
            if r.is_empty:
                continue
            if fragment:
                frag_anchors[int(a["page"])].append((a, r))
            elif h.get("unit") == "table":
                cell_boxes[int(a["page"])].append(r)
            else:
                per_page[int(a["page"])].append(r)
    for pno, members in frag_anchors.items():      
        page = doc[pno - 1]
        boxes = _formula_boxes([r for _, r in members], _page_graphics(page, caches["graphics"]))
        for a, r in members:
            host = next((b for b in boxes if b.contains(r)), r)
            if host != r:
                counts["fragment_boxes_widened"] += 1
            a["drawn"] = [round(v, 1) for v in (host.x0, host.y0, host.x1, host.y1)]   # the HTML viewer shows the same box
        per_page[pno].extend(boxes)
    n = 0
    for pno in cell_boxes:
        per_page.setdefault(pno, [])
    for pno, rects in sorted(per_page.items()):
        page = doc[pno - 1]
        merged = sorted(_merge_rects(rects), key=lambda r: (r.y0, r.x0))
        counts["boxes_merged_away"] += len(rects) - len(merged)
        merged += sorted(cell_boxes.get(pno, []), key=lambda r: (r.y0, r.x0))   # adjacent cells stay separate boxes
        for r in merged:
            if _annot_rect(page, r, rgb, title, note):
                n += 1
        if merged and _place_label(page, merged[0], label, rgb, caches["placed"].setdefault((side, pno), []),
                                   _page_text_left(page, caches["left"])):
            counts[f"labels_{side}"] += 1
    for h in (ch.get("hunks") or [ch]):          # exact place: the changed words, filled darker, no popup of their own
        for w in h.get(f"{side}_words", []) or []:
            try:
                page = doc[int(w["page"]) - 1]
            except Exception:
                continue
            if _annot_rect(page, w["bbox"], rgb, title, "", opacity=0.42, width=0.0, popup=False):
                counts[f"words_{side}"] += 1
    g = ch.get(f"{side}_gap_geometry")
    if g:
        try:
            page = doc[int(g["page"]) - 1]
        except Exception:
            page = None
        if page is not None:
            strip_note = "추가된 내용이 이 판에서 들어갈 자리" if side == "old" else "삭제된 내용이 이 판에서 있던 자리"
            if g.get("note"):
                strip_note += f" ({g['note']})"
            if _annot_rect(page, g["bbox"], rgb, title, f"[{label}] {strip_note}", opacity=0.28, width=1.5):
                n += 1
                if _place_label(page, fitz.Rect(g["bbox"]), label, rgb,            
                                caches["placed"].setdefault((side, int(g["page"])), []), _page_text_left(page, caches["left"])):
                    counts[f"labels_{side}"] += 1
    return n


def highlight_pdfs(old_path: Path, new_path: Path, changes: list[dict], out_dir: Path, stamp: str,
                   items: Optional[list] = None, page_labels: Optional[tuple] = None) -> tuple:
    """Highlighted copies of both PDFs.

    Colour = FOREWORD item; label 'a)-12' in the margin beside the first box of each change on a page (the report's
    change number); every box carries a popup note; boxes of one change are merged when adjacent; a fragment box is
    widened to the figure/formula drawing it sits in; a legend page is appended. Fragment anchors stay as they are in
    the JSON - only the drawing is simplified.
    """
    items = list(items or [])
    markers = [it["marker"] for it in items] or sorted({c.get("foreword_item", "") for c in changes})
    for c in changes:
        c.setdefault("label", f"{c.get('foreword_item', '')}{c['hunk_id']}")
    old_doc, new_doc = fitz.open(old_path), fitz.open(new_path)
    counts = {"old": 0, "new": 0, "labels_old": 0, "labels_new": 0, "words_old": 0, "words_new": 0,
              "boxes_merged_away": 0, "fragment_boxes_widened": 0}
    caches = {"graphics": {}, "left": {}, "placed": {}}
    try:
        for ch in changes:   # drawings are read before any annotation is added
            for h in (ch.get("hunks") or [ch]):
                if not (h.get("kind") == "fragment" or h.get("unit") == "fragments"):
                    continue
                for side, doc in (("old", old_doc), ("new", new_doc)):
                    for a in h.get(f"{side}_anchors", []) or []:
                        try:
                            _page_graphics(doc[int(a["page"]) - 1], caches["graphics"])
                        except Exception:
                            pass
        for ch in changes:
            rgb = item_rgb(ch.get("foreword_item", ""), markers)
            label = ch["label"]
            title = f"{label} · {ch['hunk_id']}"
            note = (f"[{label}] {CHANGE_TYPE_KO.get(ch.get('change_type'), ch.get('change_type'))} · "
                    f"{_plain_math(clean(ch.get('title_ko', '')))}\n{_plain_math(clean(ch.get('technical_difference_ko', '')))}")
            for side, doc in (("old", old_doc), ("new", new_doc)):
                counts[side] += _draw_change(doc, side, ch, rgb, label, title, note, caches, counts)
        _append_legend(old_doc, items, markers, "OLD")
        _append_legend(new_doc, items, markers, "NEW")
        old_out = out_dir / f"IEC_revision_v7_0_OLD_highlighted_{stamp}.pdf"
        new_out = out_dir / f"IEC_revision_v7_0_NEW_highlighted_{stamp}.pdf"
        for d in (old_doc, new_doc):
            try:
                d.subset_fonts()   # keep only the glyphs the legend uses of the system font (else ~13 MB per file)
            except Exception:
                pass
        old_doc.save(old_out, garbage=3, deflate=True)
        new_doc.save(new_out, garbage=3, deflate=True)
        _log_event("HIGHLIGHT_DONE", **counts)
        return old_out, new_out, counts
    finally:
        old_doc.close()
        new_doc.close()


PAGE_IMAGE_ZOOM = 1.4        # 595 x 842 pt -> 833 x 1179 px: readable body type, ~100 KB per page as JPEG
PAGE_IMAGE_QUALITY = 70


def render_page_images(pdf_path: Path, out_dir: Path, stamp: str, side: str) -> dict:
    """Page images of the ORIGINAL (un-annotated) PDF for the report's viewer, one JPEG per page in
    <out_dir>/IEC_revision_v7_0_<stamp>_pages/<side>_<page>.jpg. The viewer draws only the boxes of the change the
    reader clicked over these images, so the images themselves carry no marks. Returns the folder name, the file
    name pattern and every page's size in points (box coordinates are converted to percentages with it)."""
    folder = Path(out_dir) / f"IEC_revision_v7_0_{stamp}_pages"
    folder.mkdir(parents=True, exist_ok=True)
    sizes: dict = {}
    doc = fitz.open(pdf_path)
    try:
        for i, page in enumerate(doc, start=1):
            pix = page.get_pixmap(matrix=fitz.Matrix(PAGE_IMAGE_ZOOM, PAGE_IMAGE_ZOOM), alpha=False)
            pix.save(str(folder / f"{side}_{i:03d}.jpg"), output="jpg", jpg_quality=PAGE_IMAGE_QUALITY)
            sizes[i] = [round(float(page.rect.width), 2), round(float(page.rect.height), 2)]
    finally:
        doc.close()
    total = sum(f.stat().st_size for f in folder.glob(f"{side}_*.jpg"))
    _log_event("PAGE_IMAGES_DONE", side=side, pages=len(sizes), bytes=total, folder=folder.name)
    return {"dir": folder.name, "pattern": side + "_{page:03d}.jpg", "sizes": sizes, "count": len(sizes), "bytes": total}


# ============================================================
# HTML report (relative PDF links so the three files can be shared together)
# ============================================================

def _pdf_href(pdf: Path, base_dir: Optional[Path], page: Optional[int] = None) -> str:
    pdf = Path(pdf)
    href = None
    if base_dir is not None:
        try:
            rel = os.path.relpath(pdf.resolve(), Path(base_dir).resolve())
            if not rel.startswith(".."):
                href = urllib.parse.quote(rel.replace(os.sep, "/"))
        except ValueError:
            href = None
    if href is None:
        href = pdf.resolve().as_uri()
    return href + (f"#page={int(page)}" if page else "")


def _diff_html(old_text: str, new_text: str) -> tuple[str, str]:
    """Token-level diff rendered as <del>/<ins> (Ratcliff/Obershelp via difflib). Words are compared in their
    comparison form (norm_cmp) but displayed as written in the PDF (original case and symbols)."""
    wa, wb = clean(old_text).split(), clean(new_text).split()
    ka, kb = [norm_cmp(w) for w in wa], [norm_cmp(w) for w in wb]
    sm = difflib.SequenceMatcher(None, ka, kb, autojunk=False)
    oa, nb = [], []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            oa.append(html.escape(" ".join(wa[i1:i2])))
            nb.append(html.escape(" ".join(wb[j1:j2])))
        else:
            if i2 > i1:
                oa.append(f"<del>{html.escape(' '.join(wa[i1:i2]))}</del>")
            if j2 > j1:
                nb.append(f"<ins>{html.escape(' '.join(wb[j1:j2]))}</ins>")
    return " ".join(oa), " ".join(nb)


def _page_text(p, labels: Optional[dict]) -> str:
    """'p.12 (인쇄 10)': PDF page index plus the number printed on the page when they differ."""
    lab = None
    if labels:
        lab = labels.get(str(p)) if labels.get(str(p)) is not None else labels.get(p)
    return f"p.{p}" + (f" (인쇄 {lab})" if lab is not None and str(lab) != str(p) else "")


def _kinds_ko(kinds: str) -> str:
    return ", ".join(KIND_KO.get(k.strip(), k.strip()) for k in str(kinds or "").split(",") if k.strip())


def _slug(label: str) -> str:
    return "chg-" + re.sub(r"[^0-9A-Za-z]+", "-", str(label or "")).strip("-")


def _page_label(p, labels: Optional[dict]) -> Optional[str]:
    if not labels:
        return None
    v = labels.get(str(p)) if labels.get(str(p)) is not None else labels.get(p)
    return None if v is None or str(v) == str(p) else str(v)


def _page_range_text(pages: list, labels: Optional[dict]) -> str:
    """'p.26–27 (인쇄 24–25)': the pages of one change on one side, as one range."""
    pages = sorted({int(p) for p in pages})
    if not pages:
        return ""
    rng = f"p.{pages[0]}" if len(pages) == 1 else f"p.{pages[0]}–{pages[-1]}"
    la, lb = _page_label(pages[0], labels), _page_label(pages[-1], labels)
    if la is not None:
        rng += f" (인쇄 {la})" if (len(pages) == 1 or lb is None or la == lb) else f" (인쇄 {la}–{lb})"
    return rng


def _page_buttons(rec: dict, old_pdf: Path, new_pdf: Path, base_dir: Path, labels: tuple = (None, None), viewer: bool = False) -> str:
    """One button per edition. With page images it opens the viewer on the first page of the change, showing that
    change's boxes only (the reader pages on from there); the small PDF link beside it opens the highlighted PDF.
    A side that has no text of its own gets its insertion / deletion band instead, or no button at all."""
    ol, nl = labels
    label = rec.get("label", "")
    out = []
    for side, pdf, lab in (("old", old_pdf, ol), ("new", new_pdf, nl)):
        pages = sorted({int(p) for p in rec.get(f"{side}_pages", []) or []})
        gap = rec.get(f"{side}_gap_geometry")
        if pages:
            first, text = pages[0], f"{side.upper()} {_page_range_text(pages, lab)}"
        elif gap:
            first = int(gap["page"])
            kind = ('삽입' if side == 'old' else '삭제') + ' 자리' if gap.get("basis") != "sibling" else "추정 자리"
            text = f"{side.upper()} {kind} {_page_text(first, lab)}"
        else:
            continue
        href = html.escape(_pdf_href(pdf, base_dir, first))
        tip = html.escape(gap.get("note", "")) if (gap and not pages) else ""
        if viewer:
            out.append(f'<span class="btnpair"><button type="button" class="btn view" data-label="{html.escape(label)}" data-side="{side}" '
                       f'data-page="{first}" title="{tip}">{html.escape(text)}</button><a class="pdf" href="{href}" title="하이라이트 PDF의 이 쪽을 엽니다">PDF</a></span>')
        else:
            out.append(f'<a class="btn" href="{href}">{html.escape(text)}</a>')
    return f'<div class="links">{"".join(out)}</div>' if out else '<div class="muted">표시된 PDF 위치 없음</div>'


def _hunk_diff_html(h: dict) -> str:
    old_h, new_h = _diff_html(h.get("old_text", ""), h.get("new_text", ""))
    reason = html.escape(_plain_math(h.get("reason_ko", "") or ""))
    ct = h.get("change_type", "")
    head = (f'<div class="hunkhead"><span>{html.escape(CHANGE_TYPE_KO.get(ct, ct))}</span><span>{html.escape(_kinds_ko(h.get("kind", "")))}</span>'
            f'<span class="muted">{html.escape(h["hunk_id"])}</span>{f"<span class=\"muted\">{reason}</span>" if reason else ""}</div>')
    grid = (f'<div class="egrid"><div class="ev"><b>OLD 원문</b><div class="txt">{old_h or "<span class=\"muted\">(없음)</span>"}</div></div>'
            f'<div class="ev"><b>NEW 원문</b><div class="txt">{new_h or "<span class=\"muted\">(없음)</span>"}</div></div></div>')
    if h.get("unit") == "fragments" or h.get("kind") == "fragment":
        n = h.get("member_count") or ""
        grid = (f'<div class="muted">수식·표·그림 조각 {n}개 묶음입니다. 텍스트 비교는 기호 나열의 비교라 LLM 사유도 추정입니다. 페이지 버튼이나 아래 그림으로 확인하세요.</div>'
                f'<details><summary class="muted">추출 텍스트 비교 보기</summary>{grid}</details>')
    return f'<div class="hunk">{head}{grid}{_vlm_html(h.get("vlm"))}</div>'


VLM_KIND_KO = {"symbol_renamed": "기호 이름만 바뀜", "term_added": "항 추가", "term_removed": "항 삭제", "structure_changed": "구조 바뀜",
               "value_changed": "숫자 바뀜", "numbering_or_layout_only": "번호·배치만"}


def _vlm_html(v: Optional[dict]) -> str:
    """Reference block of the vision-model comparison: the crops of both editions beside the fixed-schema answer."""
    if not v:
        return ""
    if v.get("error"):
        return f'<div class="vlm"><b>참고(VLM {html.escape(v.get("model", ""))})</b> <span class="muted">오류: {html.escape(v["error"])}</span></div>'
    same_ko = {"yes": "같음(번호·배치 차이 제외)", "no": "다름", "unsure": "불확실"}.get(v.get("same"), "불확실")
    chg = "".join(f"<li>{html.escape(VLM_KIND_KO.get(c.get('kind'), c.get('kind', '')))}: "
                  f"{html.escape(str(c.get('old', '')))} → {html.escape(str(c.get('new', '')))}</li>" for c in v.get("changes", []))
    imgs = "".join(f'<figure><img src="data:image/png;base64,{b}" alt="OLD"><figcaption>OLD p.{c["page"]}</figcaption></figure>'
                   for c, b in zip(v.get("old_crops", []), v.get("old_crops_png", [])))
    imgs += "".join(f'<figure><img src="data:image/png;base64,{b}" alt="NEW"><figcaption>NEW p.{c["page"]}</figcaption></figure>'
                    for c, b in zip(v.get("new_crops", []), v.get("new_crops_png", [])))
    conf = v.get("confidence")
    note = " · 답이 자기모순이라 불확실로 처리" if v.get("inconsistent") else ""
    return (f'<div class="vlm"><div><b>참고(VLM {html.escape(v.get("model", ""))})</b> — 그림을 읽은 결과이며 검증되지 않았고 항목 배정에는 쓰지 않았습니다. '
            f'판정: <b>{same_ko}</b>{html.escape(note)}' + (f' · VLM 확신도 {float(conf):.2f}' if conf is not None else "") + '</div>'
            f'<div class="vlmimgs">{imgs}</div>'
            f'<div class="egrid"><div class="ev"><b>OLD 전사(VLM)</b><div class="txt">{html.escape(v.get("old_transcription", ""))}</div></div>'
            f'<div class="ev"><b>NEW 전사(VLM)</b><div class="txt">{html.escape(v.get("new_transcription", ""))}</div></div></div>'
            + (f"<ul>{chg}</ul>" if chg else "") + '</div>')


def _change_html(rec: dict, old_pdf: Path, new_pdf: Path, base_dir: Path, labels: tuple = (None, None), color: str = "#315c91",
                 viewer: bool = False, related: Optional[list] = None) -> str:
    loc = f"{html.escape(rec.get('old_location') or '—')} → {html.escape(rec.get('new_location') or '—')}"
    conf = rec.get("confidence")
    chips = f'<span class="lbl" style="color:{color};border-color:{color}">{html.escape(rec.get("label", ""))}</span>'
    chips += "".join(f"<span>{html.escape(CHANGE_TYPE_KO.get(t, t))}</span>" for t in rec.get("change_types") or [rec["change_type"]])
    chips += f"<span>{html.escape(_kinds_ko(rec.get('kind', '')))}</span>"
    if rec.get("hunk_count", 1) > 1:
        chips += f"<span>차이 {rec['hunk_count']}곳</span>"
    if rec.get("section_moved"):
        chips += "<span>절 이동</span>"
    if rec.get("hunks_reclassified"):
        chips += f"<span title=\"재생성 때 현행 규칙으로 편집상·전역 통일로 빠진 차이 (해설 글에는 남아 있을 수 있음)\">규칙으로 뺀 차이 {rec['hunks_reclassified']}곳</span>"
    chips += "<span>의미 변화</span>" if rec.get("meaning_changed") else "<span>편집·구조</span>"
    if conf is not None:
        chips += f"<span title=\"LLM이 스스로 매긴 값이며 측정된 정확도가 아닙니다\">LLM 확신도 {float(conf):.2f}</span>"
    if not rec.get("explained", True):
        chips += "<span>해설 없음(선별 사유로 대체)</span>"
    for other in related or []:        # the same clause pair also carries changes under another FOREWORD item
        chips += f'<span>같은 절: <a href="#{_slug(other)}">{html.escape(other)}</a></span>'
    hunks = rec.get("hunks") or [rec]
    return f"""
    <section class="change" id="{_slug(rec.get('label', rec.get('hunk_id', '')))}">
      <div class="chghead">{chips}<b>{html.escape(_plain_math(rec.get('title_ko')) or '(제목 없음)')}</b></div>
      <div class="loc">{loc}</div>
      {_page_buttons(rec, old_pdf, new_pdf, base_dir, labels, viewer)}
      <div class="four">
        <div><strong>OLD 의미</strong><p>{html.escape(_plain_math(rec.get('old_meaning_ko', '')))}</p></div>
        <div><strong>NEW 의미</strong><p>{html.escape(_plain_math(rec.get('new_meaning_ko', '')))}</p></div>
        <div><strong>정확한 기술 차이</strong><p>{html.escape(_plain_math(rec.get('technical_difference_ko', '')))}</p></div>
        <div><strong>엔지니어링 의미</strong><p>{html.escape(_plain_math(rec.get('engineering_significance_ko', '')))}</p></div>
      </div>
      {''.join(_hunk_diff_html(h) for h in hunks)}
    </section>"""


def _table_rows(recs: list[dict], old_pdf: Path, new_pdf: Path, base_dir: Path, labels: tuple = (None, None), label_key: str = "title_ko") -> str:
    ol, nl = labels
    rows = []
    for r in recs:
        op = r.get("old_pages") or []
        np_ = r.get("new_pages") or []
        olink = f'<a href="{html.escape(_pdf_href(old_pdf, base_dir, op[0]))}">{_page_text(op[0], ol)}</a>' if op else "—"
        nlink = f'<a href="{html.escape(_pdf_href(new_pdf, base_dir, np_[0]))}">{_page_text(np_[0], nl)}</a>' if np_ else "—"
        rc = r.get("rule_class", "")
        flag = ""
        if r.get("llm_missing"):
            flag = "[응답 누락] "
        elif r.get("region_mismatch"):
            flag = f"[후보 밖 항목 {r['region_mismatch']} 주장] "
        elif r.get("dropped_no_meaning"):
            flag = f"[{r['dropped_no_meaning']} 답했으나 의미 변화 없음 → 제외] "
        elif r.get("dropped_op"):
            flag = f"[{r['dropped_op']}의 선언 동사에 맞지 않는 변경 → 제외] "
        rows.append(f"<tr><td>{html.escape(r['hunk_id'])}</td><td>{html.escape(RULE_KO.get(rc, rc))}</td>"
                    f"<td>{html.escape(r.get('new_location') or r.get('old_location') or '')}</td>"
                    f"<td>{html.escape(flag + _plain_math(r.get(label_key) or ''))}</td>"
                    f"<td class='txt'>{html.escape(r.get('old_text', ''))}</td><td class='txt'>{html.escape(r.get('new_text', ''))}</td>"
                    f"<td>{olink} / {nlink}</td></tr>")
    return "".join(rows)


VIEWER_CSS = """
#viewer{position:fixed;inset:0;background:rgba(20,26,34,.55);z-index:50;display:flex;align-items:center;justify-content:center;padding:14px}
#viewer[hidden]{display:none}
.vwrap{background:#fff;border-radius:16px;width:min(1500px,100%);height:min(96vh,1200px);display:flex;flex-direction:column;overflow:hidden;box-shadow:0 20px 60px rgba(0,0,0,.35)}
.vhead{display:flex;gap:10px;align-items:center;padding:10px 14px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.vhead b{font-size:15px} .vhead .muted{flex:1;min-width:120px} .vhead label{font-size:12px;color:var(--muted)}
#vlbl{font:800 12px ui-monospace,monospace;border:1.5px solid;border-radius:7px;padding:1px 7px;background:#fff}
#vclose{border:1px solid var(--line);background:#fff;border-radius:8px;padding:5px 10px;cursor:pointer;font-weight:700}
.vcols{display:grid;grid-template-columns:1fr 1fr;gap:10px;padding:10px;flex:1;min-height:0}
.vcol{display:flex;flex-direction:column;min-height:0;border:1px solid var(--line);border-radius:12px;overflow:hidden;background:var(--soft)}
.vnav{display:flex;gap:6px;align-items:center;padding:6px 8px;border-bottom:1px solid var(--line);flex-wrap:wrap;font-size:12px;background:#fff}
.vnav button{border:1px solid var(--line);background:#fff;border-radius:7px;padding:2px 8px;cursor:pointer;font-size:12px;font-family:inherit}
.vnav .vchip.on{background:var(--text);color:#fff;border-color:var(--text)} .vnav .vpdf{margin-left:auto;font-size:12px}
.vscroll{overflow:auto;flex:1;min-height:0;padding:8px} .vmsg{padding:14px;color:var(--muted);font-size:13px}
.vpg{position:relative;width:100%;background:#fff;box-shadow:0 1px 4px rgba(0,0,0,.15)} .vpg img{display:block;width:100%;height:100%}
.vbox{position:absolute;box-sizing:border-box} .vbox.other{cursor:pointer}
.vboxes{position:absolute;inset:0}
.vtag{position:absolute;right:100%;top:-2px;margin-right:3px;color:#fff;font:800 11px ui-monospace,monospace;padding:1px 6px;border-radius:5px;white-space:nowrap}
.vfoot{padding:6px 14px 10px;color:var(--muted);font-size:12px}
.btnpair{display:inline-flex;align-items:stretch} .btnpair .btn{border-radius:9px 0 0 9px;cursor:pointer;background:#fff;font-family:inherit}
.btnpair .pdf{border:1px solid var(--line);border-left:none;border-radius:0 9px 9px 0;padding:6px 8px;font-size:12px;text-decoration:none;color:var(--muted);display:flex;align-items:center}
.idx{margin-top:14px} .idx table{margin-top:8px} .idx td .links{margin-top:0} .idx td.loc{margin:0} .idx th,.idx td:nth-child(2),.idx td:nth-child(5){white-space:nowrap}
.idx .lbl{font:800 12px ui-monospace,monospace;border:1.5px solid;border-radius:7px;padding:1px 7px;background:#fff;text-decoration:none}
.block{border:1px solid var(--line);border-radius:12px;padding:12px 14px;margin-top:14px;background:var(--soft)}
.bhead{display:flex;gap:10px;align-items:center;flex-wrap:wrap} .bhead .links{margin-top:0} .bhead b{font-size:15px}
.bidx{font-size:11px;font-weight:800;border:1.5px solid;border-radius:999px;padding:2px 8px;background:#fff;white-space:nowrap}
.bmem{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px} .bmem a{font-size:12px;border:1px solid var(--line);border-radius:12px;padding:2px 8px;background:#fff;text-decoration:none;color:var(--text);max-width:100%}
.bdet{margin-top:8px} .bdet>summary{font-size:13px;color:var(--muted)} .bdet .change{background:#fff;border:1px solid var(--line);border-radius:11px;padding:12px;margin-top:10px}
@media(max-width:800px){.vcols{grid-template-columns:1fr}}
"""

REVEAL_JS = r"""
(function(){
  function reveal(){ var id; try { id = decodeURIComponent(location.hash.slice(1)); } catch (e) { return; }
    if (!id || id.indexOf('view=') === 0) return; var el = document.getElementById(id); if (!el) return;
    var d = el.parentElement; while (d) { if (d.tagName === 'DETAILS') d.open = true; d = d.parentElement; }
    el.scrollIntoView({block: 'start'}); }
  window.addEventListener('hashchange', reveal); reveal();
})();
"""

VIEWER_HTML = """
<div id="viewer" hidden>
 <div class="vwrap">
  <div class="vhead"><span id="vlbl"></span><b id="vtitle"></b><span class="muted" id="vloc"></span>
   <label><input type="checkbox" id="vothers"> 같은 쪽의 다른 변경도 회색으로 표시</label>
   <button type="button" id="vclose">닫기 ✕</button></div>
  <div class="vcols">""" + "".join(f"""
   <div class="vcol" data-side="{side}"><div class="vnav"><b>{side.upper()}</b><button type="button" class="vprev">◀</button><span class="vpage"></span>
    <button type="button" class="vnext">▶</button><span class="vpages"></span><a class="vpdf" target="_blank" href="#">PDF에서 열기</a></div>
    <div class="vscroll"><div class="vmsg"></div><div class="vpg"><img alt=""><div class="vboxes"></div></div></div></div>""" for side in ("old", "new")) + """
  </div>
  <div class="vfoot">색 상자 = 이 변경이 걸린 줄 · 진한 채움 = 바뀐 단어 · 점선 띠 = 상대 판에서 들어갈(있던) 자리 · 점선 테두리 = 수식·표·그림 조각 전체. ◀ ▶ 로 앞뒤 쪽을 넘겨 이어지는 내용을 볼 수 있습니다 (Esc 닫기, ←/→ NEW 쪽 넘김).</div>
 </div>
</div>
"""

VIEWER_JS = r"""
(function(){
  var D = JSON.parse(document.getElementById('vdata').textContent || '{}');
  var V = document.getElementById('viewer');
  if (!V || !D.pages || !D.pages.old) { return; }
  var cur = {label: null, labels: [], page: {old: 0, new: 0}};
  var byPage = {old: {}, new: {}};
  D.order.forEach(function(l){ ['old', 'new'].forEach(function(s){ var e = D.changes[l][s]; if (!e) return; var ps = {};
    e.boxes.forEach(function(b){ ps[b.p] = 1; }); if (e.gap) ps[e.gap.p] = 1;
    Object.keys(ps).forEach(function(p){ (byPage[s][p] = byPage[s][p] || []).push(l); }); }); });
  function rgba(hex, a){ var n = parseInt(hex.replace('#', ''), 16); return 'rgba(' + ((n >> 16) & 255) + ',' + ((n >> 8) & 255) + ',' + (n & 255) + ',' + a + ')'; }
  function pageText(side, p){ var lab = D.pages[side].labels || {}; var v = lab[String(p)]; return 'p.' + p + (v !== undefined && String(v) !== String(p) ? ' (인쇄 ' + v + ')' : ''); }
  function imgSrc(side, p){ var s = String(p); while (s.length < 3) s = '0' + s; return D.pages[side].dir + '/' + D.pages[side].pattern.replace('{page:03d}', s); }
  function col(side){ return V.querySelector('.vcol[data-side="' + side + '"]'); }
  function current(side){
    var out = {boxes: [], pages: {}, gap: null, pdf: null, color: null};
    cur.labels.forEach(function(l){ var ch = D.changes[l], e = ch && ch[side]; if (!e) return;
      e.boxes.forEach(function(b){ out.boxes.push({b: b, label: l, color: ch.color}); });
      e.pages.forEach(function(q){ out.pages[q] = 1; });
      if (e.gap && !out.gap) { out.gap = e.gap; out.gapLabel = l; }
      if (e.pdf) out.pdf = e.pdf; if (!out.color) out.color = ch.color; });
    out.pages = Object.keys(out.pages).map(Number);
    if (out.gap && out.pages.indexOf(out.gap.p) < 0) out.pages.push(out.gap.p);
    out.pages.sort(function(a, b){ return a - b; });
    return out;
  }
  function render(side){
    var c = col(side), p = cur.page[side], e = current(side);
    var sz = D.pages[side].sizes[String(p)];
    var pg = c.querySelector('.vpg'), img = pg.querySelector('img'), bx = pg.querySelector('.vboxes'), msg = c.querySelector('.vmsg');
    c.querySelector('.vpage').textContent = pageText(side, p);
    if (e.pdf) c.querySelector('.vpdf').href = e.pdf + '#page=' + p;
    if (!sz) { pg.style.display = 'none'; msg.textContent = '쪽 이미지가 없습니다.'; return; }
    pg.style.display = ''; msg.textContent = (e.gap && e.gap.p === p && e.gap.note) ? '자리 근거: ' + e.gap.note : '';
    pg.style.aspectRatio = sz[0] + ' / ' + sz[1];
    if (img.getAttribute('src') !== imgSrc(side, p)) img.src = imgSrc(side, p);
    bx.innerHTML = '';
    var W = sz[0], H = sz[1];
    function box(b, kind, title, color, onclick){
      var d = document.createElement('div'); d.className = 'vbox ' + kind;
      d.style.left = (b[0] / W * 100) + '%'; d.style.top = (b[1] / H * 100) + '%';
      d.style.width = ((b[2] - b[0]) / W * 100) + '%'; d.style.height = ((b[3] - b[1]) / H * 100) + '%';
      if (kind === 'line') { d.style.border = '2px solid ' + color; d.style.background = rgba(color, 0.16); }
      else if (kind === 'frag') { d.style.border = '2px dashed ' + color; d.style.background = rgba(color, 0.12); }
      else if (kind === 'word') { d.style.background = rgba(color, 0.45); d.style.borderRadius = '2px'; }
      else if (kind === 'gap') { d.style.borderTop = '3px dashed ' + color; d.style.background = rgba(color, 0.25); }
      else { d.style.border = '1px solid rgba(90,90,90,.75)'; d.style.background = 'rgba(0,0,0,.05)'; }
      if (title) d.title = title; if (onclick) d.onclick = onclick;
      bx.appendChild(d); return d;
    }
    if (V.querySelector('#vothers').checked) {
      (byPage[side][String(p)] || []).forEach(function(l){ if (cur.labels.indexOf(l) >= 0) return; var o = D.changes[l];
        o[side].boxes.forEach(function(b){ if (b.p !== p || b.k === 'word') return; box(b.b, 'other', l + ' · ' + o.title, o.color, function(){ openViewer(l, side, p); }); }); });
    }
    var first = null, tagged = {};
    function tag(d, label, color){ var t = document.createElement('span'); t.className = 'vtag'; t.textContent = label; t.style.background = color; d.appendChild(t); }
    e.boxes.forEach(function(x){ var b = x.b; if (b.p !== p) return; var d = box(b.b, b.k, x.label + ' · ' + b.h, x.color);
      if (b.k !== 'word') { if (!first) first = d; if (!tagged[x.label]) { tagged[x.label] = 1; tag(d, x.label, x.color); } } });
    if (e.gap && e.gap.p === p) { var g = box(e.gap.b, 'gap', (side === 'old' ? '추가된 내용이 이 판에서 들어갈 자리' : '삭제된 내용이 이 판에서 있던 자리') + (e.gap.note ? ' — ' + e.gap.note : ''), e.color);
      tag(g, e.gapLabel || cur.labels[0], e.color); if (!first) first = g; }
    if (first) { setTimeout(function(){ try { first.scrollIntoView({block: 'center'}); } catch (err) {} }, 0); }
    var chips = c.querySelector('.vpages'); chips.innerHTML = '';
    var pages = e.pages.slice();
    pages.forEach(function(q){ var b = document.createElement('button'); b.type = 'button'; b.className = 'vchip' + (q === p ? ' on' : '');
      b.textContent = pageText(side, q); b.onclick = function(){ cur.page[side] = q; render(side); }; chips.appendChild(b); });
  }
  function openViewer(label, side, page, title){
    var labels = String(label).split('|').filter(function(l){ return D.changes[l]; });
    if (!labels.length) return;
    cur.label = labels[0]; cur.labels = labels;
    var ch = D.changes[labels[0]], multi = labels.length > 1;
    var lbl = V.querySelector('#vlbl'); lbl.textContent = multi ? (title || ('변경 ' + labels.length + '건')) : labels[0]; lbl.style.color = ch.color; lbl.style.borderColor = ch.color;
    V.querySelector('#vtitle').textContent = multi ? ('블록의 변경 ' + labels.length + '건을 한 화면에: ' + labels.join(', ')) : ch.title;
    V.querySelector('#vloc').textContent = multi ? '' : (ch.type + ' · ' + ch.loc);
    ['old', 'new'].forEach(function(s){
      var e = current(s), c = col(s), has = e.boxes.length || e.gap;
      c.classList.toggle('empty', !has);
      if (!has) { c.querySelector('.vmsg').textContent = s === 'old' ? '구판에는 이 내용이 없습니다(신판에서 새로 들어감). 신판 쪽을 보세요.' : '신판에는 이 내용이 없습니다(구판에서 삭제됨). 구판 쪽을 보세요.';
        c.querySelector('.vpg').style.display = 'none'; c.querySelector('.vpages').innerHTML = ''; c.querySelector('.vpage').textContent = ''; return; }
      var p = (s === side && page) ? page : (e.pages[0] || (e.gap && e.gap.p));
      cur.page[s] = p; render(s);
    });
    V.hidden = false; document.body.style.overflow = 'hidden';
    if (!multi) { try { history.replaceState(null, '', '#view=' + encodeURIComponent(labels[0])); } catch (err) {} }
  }
  function closeViewer(){ V.hidden = true; document.body.style.overflow = ''; }
  function step(side, d){ var q = cur.page[side] + d; if (q >= 1 && q <= D.pages[side].count && !col(side).classList.contains('empty')) { cur.page[side] = q; render(side); } }
  window.openViewer = openViewer;
  document.addEventListener('click', function(ev){ var b = ev.target.closest ? ev.target.closest('button.view') : null;
    if (b) openViewer(b.getAttribute('data-labels') || b.getAttribute('data-label'), b.getAttribute('data-side'), parseInt(b.getAttribute('data-page'), 10), b.getAttribute('data-title') || ''); });
  V.querySelector('#vclose').onclick = closeViewer;
  V.addEventListener('click', function(ev){ if (ev.target === V) closeViewer(); });
  document.addEventListener('keydown', function(ev){ if (V.hidden) return; if (ev.key === 'Escape') closeViewer();
    if (ev.key === 'ArrowRight') step('new', 1); if (ev.key === 'ArrowLeft') step('new', -1); });
  V.querySelector('#vothers').onchange = function(){ ['old', 'new'].forEach(function(s){ if (!col(s).classList.contains('empty')) render(s); }); };
  V.querySelectorAll('.vprev,.vnext').forEach(function(b){ b.onclick = function(){ step(b.closest('.vcol').getAttribute('data-side'), b.classList.contains('vnext') ? 1 : -1); }; });
  var m = /#view=([^&]+)/.exec(location.hash); if (m) { try { openViewer(decodeURIComponent(m[1]), null, 0); } catch (err) {} }
})();
"""


def _loc_parts(loc) -> list:
    return [p for p in str(loc or "").split(" > ") if p]


def _parent_key(loc, own: bool) -> str:
    parts = _loc_parts(loc)
    if own or len(parts) <= 1:
        return " > ".join(parts)
    return " > ".join(parts[:-1])


def _block_key(c: dict, own: bool = False) -> tuple:
    """Changes are grouped by the clause they end up in: the parent of the NEW location; deletions, which have no
    NEW location, by the parent of the OLD location. With own=True the change's own location is the key (used to
    pull a whole added / deleted section into the block of its own subsections: 3.8 joins the 3.8.x block, C.2
    joins the C.2.x block)."""
    nk = _parent_key(c.get("new_location"), own)
    if nk:
        return ("new", nk)
    return ("old", _parent_key(c.get("old_location"), own))


def _block_title(key: tuple, members: list) -> tuple:
    side, k = key
    n = len(members)
    sk = (_loc_parts(k) or [k])[-1]
    if side == "old":
        return sk, f"삭제 {n}건"
    origins = []
    for m in members:
        o = _parent_key(m.get("old_location"), False)
        origins.append((_loc_parts(o) or ["신설"])[-1] if o else "신설")
    moved = sum(1 for m in members if m.get("section_moved"))
    added = sum(1 for m in members if not m.get("old_location"))
    if all(o == sk for o in origins):
        return sk, f"안의 변경 {n}건"
    froms = ", ".join(dict.fromkeys(o for o in origins if o not in ("신설", sk)))
    parts = [f"{froms}에서 이동 {moved}" if (moved and froms) else (f"이동 {moved}" if moved else ""),
             f"신설 {added}" if added else "", f"수정 {n - moved - added}" if n - moved - added else ""]
    detail = ", ".join(p for p in parts if p)
    if any(o == sk for o in origins):
        return sk, f"안의 변경 {n}건 ({detail})"
    return f"{froms} → {sk}" if froms else sk, f"{n}건 ({detail})"


def _member_text(m: dict) -> str:
    o = (_loc_parts(m.get("old_location")) or ["—"])[-1]
    n = (_loc_parts(m.get("new_location")) or ["—"])[-1]
    name = clean(m.get("new_title") or m.get("old_title") or "")     # the full term / title; the chip wraps if long
    if o == "—":
        return f"{n} {name} 신설"
    if n == "—":
        return f"{o} {name} 삭제"
    return f"{o}→{n} {name}" if o != n else f"{n} {name}"


def _block_buttons(members: list, old_pdf: Path, new_pdf: Path, base_dir: Path, labels: tuple, viewer: bool, title: str) -> str:
    """One OLD and one NEW button for a whole block: the viewer shows every member's boxes and pages at once."""
    ol, nl = labels
    ids = "|".join(m.get("label", "") for m in members)
    out = []
    for side, pdf, lab in (("old", old_pdf, ol), ("new", new_pdf, nl)):
        pages = sorted({int(p) for m in members for p in (m.get(f"{side}_pages") or [])})
        gap = next((m.get(f"{side}_gap_geometry") for m in members if m.get(f"{side}_gap_geometry")), None)
        if pages:
            text = f"{side.upper()} {_page_range_text(pages, lab)}"
        elif gap:                                   # a deleted / added block: the band in the other edition
            pages = [int(gap["page"])]
            kind = ('삽입' if side == 'old' else '삭제') + ' 자리' if gap.get("basis") != "sibling" else "추정 자리"
            text = f"{side.upper()} {kind} {_page_text(pages[0], lab)}"
        else:
            continue
        href = html.escape(_pdf_href(pdf, base_dir, pages[0]))
        if viewer:
            out.append(f'<span class="btnpair"><button type="button" class="btn view" data-labels="{html.escape(ids)}" data-title="{html.escape(title)}" '
                       f'data-side="{side}" data-page="{pages[0]}">{html.escape(text)}</button><a class="pdf" href="{href}">PDF</a></span>')
        else:
            out.append(f'<a class="btn" href="{href}">{html.escape(text)}</a>')
    return f'<div class="links">{"".join(out)}</div>' if out else ""


def _blocks_html(changes: list, old_pdf: Path, new_pdf: Path, base_dir: Path, labels: tuple, color: str, viewer: bool,
                 related_of: dict) -> tuple:
    """Item body as blocks: changes of one clause pair are one collapsed block with a one-line member list and
    block-level buttons; a clause pair with a single change is shown as the plain change card. Returns (html, blocks)."""
    groups: dict = {}
    order: list = []
    for c in changes:
        k = _block_key(c)
        if k not in groups:
            groups[k] = []
            order.append(k)
        groups[k].append(c)
    # a whole added / deleted section leads the block of its own subsections (3.8 with 3.8.x, C.2 with C.2.x)
    for c in list(changes):
        if c.get("change_type") in ("ADD", "DELETE") and any(h.get("unit") == "section" for h in (c.get("hunks") or [])):
            own, k = _block_key(c, own=True), _block_key(c)
            if own != k and own in groups:
                groups[k].remove(c)
                groups[own].insert(0, c)
                if not groups[k]:
                    del groups[k]
                    order.remove(k)
    out, n_blocks = [], 0
    for k in order:
        ms = groups[k]
        if len(ms) == 1:
            out.append(_change_html(ms[0], old_pdf, new_pdf, base_dir, labels, color, viewer, related_of.get(ms[0].get("label"))))
            continue
        n_blocks += 1
        title, sub = _block_title(k, ms)
        chips = "".join(f'<a href="#{_slug(m["label"])}">{html.escape(m["label"])} · {html.escape(_member_text(m))}</a>' for m in ms)
        cards = "".join(_change_html(m, old_pdf, new_pdf, base_dir, labels, color, viewer, related_of.get(m.get("label"))) for m in ms)
        labs = sorted((m.get("label", "") for m in ms), key=lambda x: int(re.sub(r"\D", "", x) or 0))
        out.append(f'<section class="block" id="blk-{_slug(labs[0])[4:]}"><div class="bhead"><span class="bidx" style="color:{color};border-color:{color}">블록 {n_blocks}</span>'
                   f'<b>{html.escape(title)}</b><span class="muted">{html.escape(sub)} · {html.escape(labs[0])} … {html.escape(labs[-1])}</span>'
                   f'{_block_buttons(ms, old_pdf, new_pdf, base_dir, labels, viewer, title)}</div>'
                   f'<div class="bmem">{chips}</div><details class="bdet"><summary>세부 변경 {len(ms)}건 펼치기</summary>{cards}</details></section>')
    return "".join(out), n_blocks


def report_html(result: dict, old_pdf: Path, new_pdf: Path, html_dir: Path) -> str:
    base_dir = Path(html_dir)
    mt = result["metrics"]
    fw = result["foreword"]
    items = result["analysis"]["items"]
    editorial = result["analysis"]["editorial"]
    fragments = result["analysis"]["fragment_groups"]
    warnings_ = result["analysis"]["warnings"]
    visual = result["analysis"].get("visual_checks", [])
    labels = (result.get("old_document", {}).get("page_labels") or {}, result.get("new_document", {}).get("page_labels") or {})
    markers = [it["marker"] for it in items]
    if any("label" not in c for it in items for c in it["changes"]):
        assign_change_labels(items)
    page_images = result.get("page_images") or {}
    viewer = bool(page_images.get("old") and page_images.get("new"))

    def metric(label, value):
        return f'<div class="metric"><b>{html.escape(str(value))}</b>{html.escape(label)}</div>'

    hs = result.get("highlight_stats", {})
    metrics_html = "".join([
        metric("FOREWORD 선언 항목", len(items)),
        metric("선언 항목에 배정된 내용 변경", sum(len(i["changes"]) for i in items)),
        metric("편집상 변경", len(editorial)),
        metric("수식·표·그림 조각 묶음(절)", len(fragments)),
        metric("절 정렬 커버리지(NEW)", f"{mt['alignment']['coverage_new']:.0%}"),
        metric("제목 인식률 OLD / NEW (목차 대비)", f"{(mt['old'].get('toc_heading_recall') or 0):.0%} / {(mt['new'].get('toc_heading_recall') or 0):.0%}"),
        metric("OLD / NEW 하이라이트 상자", f"{hs.get('old', 0)} / {hs.get('new', 0)}"),
        metric("전체 hunk(코드가 찾은 차이)", mt["hunks"]["total"]),
    ])
    warn_html = "".join(f"<li>{html.escape(w)}</li>" for w in warnings_) or "<li>없음</li>"
    legend_chips = "".join(
        f'<span style="color:{rgb_hex(item_rgb(it["marker"], markers))};border-color:{rgb_hex(item_rgb(it["marker"], markers))}">'
        f'{html.escape(it["marker"])} {html.escape(_plain_math(it.get("title_ko", "")))}</span>' for it in items)

    # Changes of one clause pair under several items: each card links to the others ("같은 절: c)-1").
    by_pair: dict = {}
    for it in items:
        for c in it["changes"]:
            by_pair.setdefault((c.get("old_location", ""), c.get("new_location", "")), []).append(c.get("label"))
    related_of = {lab: [o for o in labs if o != lab] for labs in by_pair.values() if len(labs) > 1 for lab in labs}

    item_html = []
    for it in items:
        color = rgb_hex(item_rgb(it["marker"], markers))
        changes_html, n_blocks = _blocks_html(it["changes"], old_pdf, new_pdf, base_dir, labels, color, viewer, related_of)
        idx_rows = ('<div class="muted" style="margin-top:12px">같은 절 묶음의 변경은 블록 하나로 묶었습니다. 블록의 OLD/NEW 버튼은 묶음 전체의 상자를 '
                    '한 화면에서 쪽을 넘기며 보여 주고, 세부 변경은 "펼치기"로 봅니다.</div>') if n_blocks else ""
        sp = it.get("spec", {}) or {}
        region_txt = ", ".join(sp.get("target_regions") or []) or ("문서 전체" if sp.get("whole_document") else "—")
        ctypes = "/".join(CHANGE_TYPE_KO.get(t, t) for t in (sp.get("change_types") or [])) or "제한 없음"
        pkinds = "/".join(KIND_KO.get(k, k) for k in (sp.get("paragraph_kinds") or [])) or "제한 없음"
        patterns = ", ".join(sp.get("text_patterns") or []) or "없음"
        act = it.get("action", "")
        sev = it.get("severity", "")
        item_html.append(f"""
        <article class="case">
          <div class="top"><div class="num" style="color:{color};border-color:{color}">{html.escape(it['marker'])}</div><div>
            <div class="chips"><span>{html.escape(CHANGE_TYPE_KO.get(act, act))}</span><span>{html.escape(SEVERITY_KO.get(sev, sev))}</span><span title="LLM이 스스로 매긴 값이며 측정된 정확도가 아닙니다">LLM 확신도 {it['confidence']:.2f}</span><span>변경 {len(it['changes'])}건</span></div>
            <h2>{html.escape(_plain_math(it['title_ko']))}</h2><p>{html.escape(_plain_math(it['summary_ko']))}</p></div></div>
          <div class="fore"><b>IEC FOREWORD 원문</b><br>{html.escape(_display_text(it['foreword_text']))}</div>
          <div class="muted">FOREWORD 문구에서 LLM이 도출한 검색 조건 — 찾을 영역: {html.escape(region_txt)} · 변경 유형(참고, 거르지 않음): {html.escape(ctypes)} · 단락 종류(참고): {html.escape(pkinds)} · 핵심어: {html.escape(patterns)}{' · 다른 절에서 이 영역으로 옮겨온 것도 포함' if sp.get('moved_into_region') else ''}<br>
          사례 기준: {html.escape(sp.get('evidence_rule_ko') or '—')} · 후보 {it.get('candidate_count', 0)}건 → 확인 {len(it['changes'])}건{f" · 전체 차이 통독 {it['full_scan']['scanned']}건 중 {it['full_scan']['confirmed']}건 확인" if it.get('full_scan') else ''} · 영역을 신판 절 번호로 해석: {html.escape(', '.join(it['regions']['new'][:10]) or '—')}{' …' if len(it['regions']['new']) > 10 else ''}</div>
          {idx_rows}{changes_html or '<div class="muted" style="margin-top:12px">이 항목의 사례로 확인된 변경이 없습니다.</div>'}
        </article>""")

    by_id = {r["hunk_id"]: r for r in result["analysis"].get("all_hunks") or []}
    und = [by_id[i] for i in result["analysis"].get("undeclared_discarded_ids") or [] if i in by_id]
    und_html = ""
    if und:
        und_html = (f'<details><summary>어느 항목의 사례도 아닌 변경 {len(und)}건 (보고 대상 아님 — 감사용 목록)</summary>'
                    f'<div class="muted">LLM이 NONE으로 판정했거나(사유 열), 후보 밖 항목을 답했거나, 위치 없는 항목에 의미 변화 없이 배정해 코드가 제외한 차이입니다. LLM 응답 누락도 여기에 남습니다. 무엇이 버려졌는지 확인하는 용도입니다.</div>'
                    f'<table><tr><th>ID</th><th>판정</th><th>위치</th><th>LLM 사유</th><th>OLD</th><th>NEW</th><th>페이지</th></tr>'
                    f'{_table_rows(und, old_pdf, new_pdf, base_dir, labels, label_key="reason_ko")}</table></details>')
    sys_pairs = result["analysis"].get("systematic_pairs") or []
    sys_html = ""
    if sys_pairs:
        sys_html = (f'<div class="muted" style="margin-bottom:8px">문서 전체에서 {SYSTEMATIC_MIN_HUNKS}개 이상의 단락에 되풀이되는 치환은 판 전체의 표현 통일로 보고, '
                    f'"사소한 오류 수정"처럼 위치를 지정하지 않은 항목의 통독 대상에서 뺐습니다(영역이 지정된 항목의 후보로는 남김). 숫자가 든 치환은 규칙에서 제외합니다.</div>'
                    f'<table><tr><th>OLD 표현</th><th>NEW 표현</th><th>단락 수</th></tr>'
                    + "".join(f"<tr><td>{html.escape(p['old'])}</td><td>{html.escape(p['new'])}</td><td>{p['hunks']}</td></tr>" for p in sys_pairs)
                    + '</table>')

    # Data for the viewer: every change's boxes per edition (line boxes, word runs, insertion band) and the page sizes.
    view_changes: dict = {}
    for it in items:
        color = rgb_hex(item_rgb(it["marker"], markers))
        for c in it["changes"]:
            entry = {"item": it["marker"], "color": color, "title": _plain_math(clean(c.get("title_ko", ""))),
                     "loc": f"{c.get('old_location') or '—'} → {c.get('new_location') or '—'}",
                     "type": CHANGE_TYPE_KO.get(c.get("change_type"), c.get("change_type", ""))}
            for side, pdf in (("old", old_pdf), ("new", new_pdf)):
                boxes = []
                for h in c.get("hunks") or [c]:
                    frag = h.get("kind") == "fragment" or h.get("unit") == "fragments"
                    for a in h.get(f"{side}_anchors") or []:
                        boxes.append({"p": int(a["page"]), "b": [round(float(v), 1) for v in (a.get("drawn") or a["bbox"])],
                                      "k": "frag" if frag else "line", "h": h.get("hunk_id", "")})
                    for w in h.get(f"{side}_words") or []:
                        boxes.append({"p": int(w["page"]), "b": [round(float(v), 1) for v in w["bbox"]], "k": "word", "h": h.get("hunk_id", "")})
                gap = c.get(f"{side}_gap_geometry")
                entry[side] = {"pages": sorted({int(p) for p in c.get(f"{side}_pages", []) or []}), "boxes": boxes,
                               "gap": {"p": int(gap["page"]), "b": [round(float(v), 1) for v in gap["bbox"]], "note": gap.get("note", "")} if gap else None,
                               "pdf": _pdf_href(pdf, base_dir)}
            view_changes[c["label"]] = entry
    view_data = {"changes": view_changes, "order": [c["label"] for it in items for c in it["changes"]],
                 "pages": {side: {"dir": page_images[side]["dir"], "pattern": page_images[side].get("pattern", side + "_{page:03d}.jpg"),
                                  "sizes": page_images[side]["sizes"], "count": page_images[side].get("count", len(page_images[side]["sizes"])),
                                  "labels": labels[0 if side == "old" else 1]} for side in ("old", "new")} if viewer else {}}
    view_json = json.dumps(view_data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    viewer_block = (VIEWER_HTML + f'<script id="vdata" type="application/json">{view_json}</script><script>{VIEWER_JS}</script>') if viewer else ""
    viewer_note = (" 변경 기록의 OLD/NEW 버튼은 그 변경의 상자만 색으로 그린 쪽 이미지 뷰어를 열고(◀ ▶로 이어지는 쪽을 넘김), 옆의 PDF 링크는 하이라이트 PDF의 그 쪽을 엽니다."
                   if viewer else "")

    vlm_by_hunk = {v["hunk_id"]: v for v in visual}
    vlm_stats = result.get("vlm") or {}

    def _frag_vlm(g):
        vs = [vlm_by_hunk[hid] for hid in g.get("hunk_ids", []) if hid in vlm_by_hunk]
        if not vs:
            return "—"
        return ", ".join({"yes": "같음", "no": "다름", "unsure": "불확실"}.get(v.get("same"), "오류" if v.get("error") else "불확실") for v in vs)

    frag_rows = "".join(
        f"<tr><td>{html.escape(g['section'])}</td><td>{html.escape(g['title'])}</td><td>{g['count']}</td><td>{html.escape(_frag_vlm(g))}</td>"
        f"<td>{' '.join(f'<a href=\"{html.escape(_pdf_href(old_pdf, base_dir, p))}\">{_page_text(p, labels[0])}</a>' for p in g['old_pages'][:6])}</td>"
        f"<td>{' '.join(f'<a href=\"{html.escape(_pdf_href(new_pdf, base_dir, p))}\">{_page_text(p, labels[1])}</a>' for p in g['new_pages'][:6])}</td></tr>"
        for g in fragments)
    if vlm_stats.get("enabled"):
        visual_html = (f"<div class='muted' style='margin-top:8px'>VLM 비교({html.escape(str(vlm_stats.get('model', '')))}): 대상 {vlm_stats.get('scope', 0)}건 "
                       f"(FOREWORD가 영역을 지정한 항목의 후보인 조각만), 비교 {vlm_stats.get('compared', 0)}건, 불확실 {vlm_stats.get('unsure', 0)}건, 오류 {vlm_stats.get('errors', 0)}건"
                       + (f" · 건너뜀: {html.escape(vlm_stats['skipped'])}" if vlm_stats.get("skipped") else "") + ". 결과는 해당 변경 카드의 '참고(VLM)' 칸에 그림과 함께 있습니다.</div>")
    else:
        visual_html = "<div class='muted' style='margin-top:8px'>VLM 비교는 이번 실행에서 켜지 않았습니다.</div>"
    al = result["alignment_summary"]
    align_rows = "".join(f"<tr><td>{html.escape(ALIGN_METRIC_KO.get(k, k))}<span class='muted'> {html.escape(k)}</span></td><td>{html.escape(str(v))}</td></tr>"
                         for k, v in mt["alignment"].items())
    moved_rows = "".join(f"<tr><td>{html.escape(p['old'])}</td><td>{html.escape(p['new'])}</td><td>{html.escape(p['stage'])}</td><td>{p['score']}</td></tr>" for p in al["moved"])
    del_rows = "".join(f"<li>{html.escape(x)}</li>" for x in al["deleted"])
    add_rows = "".join(f"<li>{html.escape(x)}</li>" for x in al["added"])

    return f"""<!doctype html>
<html lang="ko"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>IEC Revision Analyzer V7.0 · Hybrid structural diff</title>
<style>
:root{{--bg:#f4f6f8;--card:#fff;--text:#1f242b;--muted:#697386;--line:#dde2e8;--soft:#f8fafc;--blue:#315c91}}
*{{box-sizing:border-box}} body{{margin:0;background:var(--bg);color:var(--text);font:15px/1.6 system-ui,-apple-system,"Malgun Gothic",sans-serif}}
main{{max-width:1240px;margin:auto;padding:30px 18px 70px}} h1{{margin:0;font-size:30px}} h2{{margin:4px 0 6px;font-size:20px}} h3{{margin:28px 0 10px;font-size:18px}}
.hero,.case,.panel{{background:var(--card);border:1px solid var(--line);border-radius:18px}} .hero,.panel{{padding:20px;margin:16px 0}} .case{{padding:20px;margin:14px 0}}
.metrics{{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-top:14px}} .metric{{background:var(--soft);padding:12px;border-radius:12px;border:1px solid var(--line)}} .metric b{{font-size:24px;display:block}}
.top{{display:flex;gap:14px}} .num{{min-width:42px;height:42px;padding:0 8px;border-radius:21px;display:grid;place-items:center;border:2px solid var(--line);font-weight:800;font-size:16px;flex:none}}
.chips{{display:flex;gap:6px;flex-wrap:wrap}} .chips span,.chghead span{{font-size:11px;font-weight:800;border:1px solid var(--line);padding:2px 7px;border-radius:999px}}
.chghead span.lbl{{font:800 12px ui-monospace,monospace;border:1.5px solid;border-radius:7px;padding:1px 7px;background:#fff}} .legend span{{font-size:12px;font-weight:800;border:1.5px solid;border-radius:7px;padding:1px 7px;background:#fff}} .legend{{margin-top:12px;font-size:13px}} .legend .chips{{margin-top:6px}}
.fore{{background:var(--soft);border-radius:11px;padding:11px 13px;margin-top:14px}} .change{{border-top:1px solid var(--line);margin-top:16px;padding-top:16px}} .chghead{{display:flex;align-items:center;gap:8px;flex-wrap:wrap}}
.loc{{color:var(--muted);font:12px ui-monospace,monospace;margin-top:4px}}
.four{{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:12px}} .four>div,.ev{{border:1px solid var(--line);border-radius:11px;padding:11px;background:var(--soft)}} .four p{{margin:5px 0 0}}
.egrid{{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:10px}} .txt{{font-size:13px;line-height:1.55}} del{{background:#fde2e1;color:#8a1c1c;text-decoration:line-through}} ins{{background:#dcf5e6;color:#135c2e;text-decoration:none}}
.hunk{{margin-top:12px;padding-top:8px;border-top:1px dashed var(--line)}} .hunkhead{{display:flex;gap:6px;align-items:center;flex-wrap:wrap}} .hunkhead span{{font-size:11px;font-weight:800;border:1px solid var(--line);padding:1px 6px;border-radius:999px}} .hunkhead span.muted{{font-weight:500;border:none}}
.muted{{color:var(--muted);font-size:12px}} .links{{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}} .btn{{text-decoration:none;color:var(--text);border:1px solid var(--line);border-radius:9px;padding:6px 10px;font-weight:700;font-size:13px}}
table{{width:100%;border-collapse:collapse;font-size:12.5px}} th,td{{border-bottom:1px solid var(--line);padding:6px 8px;vertical-align:top;text-align:left}} details summary{{cursor:pointer;font-weight:700}}
.warn{{background:#fff7e6;border:1px solid #f0d9a6;border-radius:12px;padding:10px 14px}} ul{{margin:6px 0}}
.vlm{{margin-top:10px;padding:10px 12px;border:1px dashed var(--line);border-radius:11px;background:#fbfbfd;font-size:13.5px}} .vlmimgs{{display:flex;gap:10px;flex-wrap:wrap;margin-top:8px}} .vlmimgs figure{{margin:0;border:1px solid var(--line);border-radius:8px;padding:6px;background:#fff;max-width:48%}} .vlmimgs img{{max-width:100%;height:auto;display:block}} .vlmimgs figcaption{{font-size:11px;color:var(--muted);margin-top:4px}}
@media(max-width:800px){{.metrics,.four,.egrid{{grid-template-columns:1fr}}}}
{VIEWER_CSS}</style></head><body><main>
<h1>IEC Revision Analyzer V7.0 · FOREWORD 우선 + 구조 diff</h1>
<div class="muted">{html.escape(result['old_document']['filename'])} → {html.escape(result['new_document']['filename'])} · 모델 {html.escape(result['model'])} · {html.escape(result['created_at'])}</div>
<section class="hero"><strong>CODE가 두 판의 절·정의를 정렬해 모든 텍스트 차이를 찾고, LLM은 각 차이의 의미 변화 여부와 FOREWORD 항목 배정, 기술 해설만 판단합니다.</strong>
<div class="metrics">{metrics_html}</div>
<div class="links"><a class="btn" href="{html.escape(_pdf_href(old_pdf, base_dir))}">OLD highlighted PDF</a><a class="btn" href="{html.escape(_pdf_href(new_pdf, base_dir))}">NEW highlighted PDF</a></div>
<div class="muted" style="margin-top:8px">PDF 링크는 이 HTML과 같은 폴더의 하이라이트 PDF를 가리킵니다. 공유할 때는 HTML과 PDF 2개를 함께 보내세요.</div>
<div class="legend"><b>PDF 하이라이트 읽는 법</b> — 상자 색은 FOREWORD 항목, 상자 왼쪽 여백의 라벨(예: a)-12)은 아래 1절의 변경 번호입니다. 가는 띠는 추가(삭제)된 내용이 상대 판에서 들어갈 자리이고, 상자 안의 진한 채움은 실제로 바뀐 단어이고, 상자를 클릭하면 요약 메모가 열립니다. 버튼의 p.N은 PDF 쪽 번호, 괄호 안 '인쇄 N'은 지면에 찍힌 쪽 번호입니다. 같은 범례가 각 PDF의 마지막 쪽에 있습니다.{viewer_note}
<div class="chips">{legend_chips}</div></div>
<div class="warn" style="margin-top:12px"><b>구조 추출·완결성 경고</b><ul>{warn_html}</ul></div></section>
<h3>1. FOREWORD 선언 항목별 내용 변경 (p.{fw.get('page')}–{fw.get('end_page')})</h3>
<div class="muted">FOREWORD 항목마다 문구에서 검색 조건을 도출해 CODE가 후보 차이를 모으고, LLM은 각 후보가 선언된 변경의 실제 사례인지만 확인했습니다. 어느 항목의 사례도 아닌 변경은 정리 대상에서 제외했습니다 (이번 실행에서 {result['analysis'].get('undeclared_discarded_count', 0)}건, JSON의 undeclared_discarded_ids에 ID만 기록). 변경 번호(예: a)-12)는 하이라이트 PDF의 라벨과 같습니다.</div>
{''.join(item_html)}
<h3>2. 수식·표·그림 조각 묶음 ({len(fragments)}개 절 — 감사용)</h3>
<article class="case"><div class="muted">텍스트 추출이 불안정한 수식·표·그림 영역은 단어 단위 비교 대상에서 제외하고 절 단위로 모았습니다. FOREWORD 항목의 영역 안에 든 묶음만 1절의 변경 카드와 VLM 비교 대상이 되고, 나머지는 어느 선언에도 속하지 않으므로 여기 목록으로만 남깁니다.</div>
<table><tr><th>절</th><th>제목</th><th>조각 수</th><th>VLM 비교</th><th>OLD 페이지</th><th>NEW 페이지</th></tr>{frag_rows}</table>
{visual_html}</article>
<h3>3. 편집상 변경 ({len(editorial)}건)</h3>
<article class="case">{sys_html}<details><summary>표 펼치기 (규칙 판정 + LLM 판정)</summary>
<table><tr><th>ID</th><th>판정</th><th>위치</th><th>라벨</th><th>OLD</th><th>NEW</th><th>페이지</th></tr>{_table_rows(editorial, old_pdf, new_pdf, base_dir, labels)}</table></details>{und_html}</article>
<h3>4. 절 정렬 결과</h3>
<article class="case"><details><summary>정렬 지표와 이동·삭제·추가 절</summary>
<div class="muted">짝짓기 단계: A = 번호와 제목이 같음(A2 = 번호 같고 제목이 거의 같음, B 다음에 적용) · B = 제목은 같고 번호만 다름(재번호·이동; 같은 제목이 여럿이면 부모의 짝 아래 것으로 = B-tree) · C = 본문 유사도(임계값은 이 문서 쌍에서 보정) · D = 본문이 없는 상위 절을 번호 또는 하위 절의 짝으로 묶음. 회색 글자는 JSON의 지표 이름입니다.</div>
<table>{align_rows}</table>
<p><b>이동/재번호 절</b></p><table><tr><th>OLD</th><th>NEW</th><th>짝지은 단계</th><th>점수</th></tr>{moved_rows}</table>
<p><b>OLD에만 있는 절 (삭제 후보)</b></p><ul>{del_rows or '<li>없음</li>'}</ul>
<p><b>NEW에만 있는 절 (추가 후보)</b></p><ul>{add_rows or '<li>없음</li>'}</ul></details></article>
</main>{viewer_block}<script>{REVEAL_JS}</script></body></html>"""


# ============================================================
# Pipeline
# ============================================================

def _run_pipeline_impl(old_path: Path, new_path: Path, base_url: str, model: str, use_visual: bool, progress=None,
                       cross_check: bool = False) -> dict:
    if fitz is None:
        raise RuntimeError("PyMuPDF가 설치되어 있지 않습니다.")
    started = time.perf_counter()
    current_pct = 0

    def emit(pct, msg):
        nonlocal current_pct
        current_pct = max(current_pct, int(round(pct)))
        _log_event("PROGRESS", percent=current_pct, message=msg)
        if progress:
            progress(f"[{current_pct:3d}%] {msg}")

    emit(1, "Ollama 모델 확인")
    if model not in ollama_list_models(base_url):
        raise RuntimeError(f"Ollama 모델 '{model}'이 설치되어 있지 않습니다.")
    emit(3, "PDF 열기")
    old_doc, new_doc = fitz.open(old_path), fitz.open(new_path)
    try:
        old_meta, new_meta = document_metadata(old_doc, old_path), document_metadata(new_doc, new_path)
        emit(5, "NEW PDF FOREWORD 개정 선언 파싱 (LLM)")
        foreword = parse_foreword_sequentially(new_doc, base_url, model, progress=lambda m_: emit(6, m_))
        emit(12, f"FOREWORD 선언 항목 {len(foreword['items'])}건 확인")

        emit(14, "구조 추출 · 정렬 · diff (CODE)")
        struct = analyse_pair_structure(old_doc, new_doc)
        hunks: list[Hunk] = struct["hunks"]
        old_meta["page_labels"] = printed_page_numbers(struct["old_prep"]["lines"])   # PDF page -> printed page number
        new_meta["page_labels"] = printed_page_numbers(struct["new_prep"]["lines"])
        emit(22, f"hunk {len(hunks)}개: " + ", ".join(f"{k} {v}" for k, v in sorted(Counter(h.rule_class for h in hunks).items())))
        emit(23, "FOREWORD 항목 → 검색 조건 도출 (LLM) → 후보 선별 (CODE)")
        specs = derive_item_specs(foreword["items"], base_url, model, struct["old"]["sections"], struct["new"]["sections"])
        regions = select_candidates(hunks, specs)
        emit(24, "후보 hunk " + ", ".join(f"{s['marker']} {sum(1 for h in hunks if s['marker'] in h.candidate_buckets)}" for s in specs))

        vlm_stats = {"model": VLM_MODEL, "enabled": bool(use_visual), "scope": 0, "compared": 0, "unsure": 0, "errors": 0, "skipped": ""}
        if use_visual:
            scope = vlm_fragment_scope(hunks, specs)
            vlm_stats["scope"] = len(scope)
            if not scope:
                vlm_stats["skipped"] = "영역이 있는 항목의 후보인 수식·그림 조각이 없음"
            elif VLM_MODEL not in ollama_list_models(base_url):
                vlm_stats["skipped"] = f"VLM 모델 '{VLM_MODEL}'이 Ollama에 없음"
            else:
                emit(25, f"VLM 수식·그림 비교 {len(scope)}건 ({VLM_MODEL})")
                vlm_compare_fragments(scope, old_doc, new_doc, base_url, VLM_MODEL, vlm_stats, progress=lambda m_: emit(26, m_))
        _log_event("VLM_STATS", **vlm_stats)

        cls = classify_hunks(hunks, foreword["items"], specs, base_url, model,
                             progress=lambda m_: emit(min(78, 24 + 54 * _progress_fraction(m_)), m_),
                             cross_check=cross_check, old_secs=struct["old"]["sections"], new_secs=struct["new"]["sections"])
        results = cls["results"]

        emit(80, "결과 조립 · ghost gap · 요약")
        beads_by_pair = {}
        pairs = struct["alignment"]["pairs"]
        for p in pairs:
            os_, ns = struct["old"]["sections"][p["old"]], struct["new"]["sections"][p["new"]]
            beads_by_pair[(os_.sid, ns.sid)] = align_paragraphs(os_.paragraphs, ns.paragraphs, struct["alignment"].get("paragraph_threshold"))
        records = []
        for h in hunks:
            rec = _hunk_record(h, results.get(h.hunk_id))
            if h.change_type == "ADD" and h.unit == "paragraph":
                rec["old_gap_geometry"] = ghost_gap_for_add(h, beads_by_pair)
            if h.change_type == "DELETE" and h.unit == "paragraph":
                rec["new_gap_geometry"] = ghost_gap_for_delete(h, beads_by_pair)
            if h.unit == "section" and h.change_type in ("ADD", "DELETE"):
                rec["old_gap_geometry" if h.change_type == "ADD" else "new_gap_geometry"] = ghost_gap_for_section(
                    h, struct["old"]["sections"], struct["new"]["sections"], pairs)
            records.append(rec)
        rec_by_id = {r["hunk_id"]: r for r in records}
        by_item: dict[str, list] = defaultdict(list)
        editorial, undeclared_ids = [], []
        markers = {it["marker"] for it in foreword["items"]}
        for rec in records:
            if rec.get("foreword_item") in markers:
                continue
            if rec.get("rule_class") in ("EDITORIAL", "RENUMBER", "SYSTEMATIC") or (rec.get("candidate_foreword_items") and not rec.get("meaning_changed")):
                editorial.append(rec)          # trivial by rule, or verified as not realising any item without meaning change
            elif rec.get("rule_class") != "FRAGMENT":
                undeclared_ids.append(rec["hunk_id"])   # discarded: not declared by the FOREWORD
        # One change record per clause / terminological entry (group of hunks explained together).
        for gid, g in cls["groups"].items():
            recs = [rec_by_id[hid] for hid in g["hunk_ids"] if hid in rec_by_id]
            if recs:
                by_item[g["foreword_item"]].append(_group_record(gid, g, recs))
        for lst in by_item.values():
            lst.sort(key=lambda r: ((r.get("new_pages") or r.get("old_pages") or [0])[0], r["group_id"]))
        items_out = []
        for idx, it in enumerate(foreword["items"], start=1):
            emit(80 + idx, f"{it['marker']} 항목 요약 (LLM)")
            changes = by_item.get(it["marker"], [])
            summary = summarise_item(it, changes, base_url, model)
            spec = next((s for s in specs if s["marker"] == it["marker"]), {})
            fs = cls["stats"].get("full_scan", {}).get(it["marker"])
            items_out.append({**it, **summary, "changes": changes, "regions": regions.get(it["marker"], {"new": [], "old": []}),
                              "spec": {k: spec.get(k) for k in ("target_regions", "change_types", "paragraph_kinds", "text_patterns",
                                                                 "moved_into_region", "whole_document", "evidence_rule_ko")},
                              "candidate_count": sum(1 for h in hunks if it["marker"] in h.candidate_buckets),
                              "full_scan": fs})
        assign_change_labels(items_out)   # 'a)-12': the report's change number, printed beside the PDF boxes
        frags = fragment_groups(hunks)
        visual = [{"hunk_id": h.hunk_id, "old_location": h.old_section.path() if h.old_section else "",
                   "new_location": h.new_section.path() if h.new_section else "", "same": h.vlm.get("same"),
                   "changes": h.vlm.get("changes", []), "confidence": h.vlm.get("confidence"), "error": h.vlm.get("error")}
                  for h in hunks if h.vlm]

        warnings_ = []
        if use_visual and vlm_stats.get("skipped"):
            warnings_.append(f"VLM 수식·그림 비교를 건너뜀: {vlm_stats['skipped']}.")
        if vlm_stats.get("errors"):
            warnings_.append(f"VLM 수식·그림 비교 오류 {vlm_stats['errors']}건 (해당 조각은 텍스트 비교만 남음).")
        for it in items_out:
            if not it["changes"]:
                warnings_.append(f"FOREWORD 항목 {it['marker']}: 후보 {it['candidate_count']}건 중 확인된 사례가 0건입니다. 검색 조건(영역 {', '.join(it['regions']['new'][:5]) or '없음'})과 정렬 표를 확인하세요.")
        for side in ("old", "new"):
            r = struct["metrics"][side].get("toc_heading_recall")
            if r is not None and r < 0.9:
                warnings_.append(f"{side.upper()} 제목 인식률이 목차 대비 {r:.0%}입니다. 구조 추출을 신뢰하기 어려운 문서일 수 있습니다.")
            elif r is None:
                warnings_.append(f"{side.upper()} 문서에서 목차를 찾지 못했습니다. 제목 인식이 활자 단서에만 의존하고, 번호를 건너뛴 제목과 굵지 않은 제목은 인정되지 않습니다.")
        if struct["metrics"]["alignment"]["coverage_new"] < 0.8:
            warnings_.append(f"NEW 절 정렬 커버리지가 {struct['metrics']['alignment']['coverage_new']:.0%}입니다. 추가/삭제 절 목록을 확인하세요.")
        missing_n = sum(1 for r in results.values() if r.get("llm_missing"))
        if missing_n:
            warnings_.append(f"LLM 응답에서 누락된 hunk {missing_n}건: 후보 항목이 하나뿐이면 그 항목 아래 '확인 필요'로, 아니면 3절의 미선언 표에 남겼습니다.")
        if cls["stats"].get("dropped_no_meaning"):
            warnings_.append(f"위치 없는 항목에 LLM이 배정했지만 기술 내용 변화가 없어 코드가 제외한 차이 {cls['stats']['dropped_no_meaning']}건 (3절 미선언 표에 사유 표시).")
        if cls["stats"].get("region_mismatch"):
            warnings_.append(f"LLM이 후보 밖 항목을 답해 NONE으로 되돌린 차이 {cls['stats']['region_mismatch']}건 (3절 미선언 표에 표시).")
        if cls["stats"].get("dropped_op"):
            warnings_.append(f"선언 동사(moved/added/deleted)에 맞지 않는 차이를 LLM이 그 항목에 배정한 {cls['stats']['dropped_op']}건을 코드가 되돌려 다른 후보로 재판정했거나 제외했습니다 (3절 미선언 표에 표시).")

        emit(90, "하이라이트 PDF 생성")
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        out_dir = new_path.parent
        all_changes = [c for it in items_out for c in it["changes"]]
        old_hl, new_hl, hl_stats = highlight_pdfs(old_path, new_path, all_changes, out_dir, stamp, items=items_out,
                                                  page_labels=(old_meta["page_labels"], new_meta["page_labels"]))
        emit(93, "보고서 뷰어용 쪽 이미지 생성")
        page_images = {"old": render_page_images(old_path, out_dir, stamp, "old"), "new": render_page_images(new_path, out_dir, stamp, "new")}

        old_secs, new_secs = struct["old"]["sections"], struct["new"]["sections"]
        alignment_summary = {
            "moved": [{"old": f"{old_secs[p['old']].number} {old_secs[p['old']].term or old_secs[p['old']].title}",
                       "new": f"{new_secs[p['new']].number} {new_secs[p['new']].term or new_secs[p['new']].title}",
                       "stage": p["stage"], "score": p["score"]} for p in pairs if p["moved"]],
            "deleted": [f"{old_secs[i].number} {old_secs[i].term or old_secs[i].title}" for i in struct["alignment"]["deleted"]],
            "added": [f"{new_secs[j].number} {new_secs[j].term or new_secs[j].title}" for j in struct["alignment"]["added"]],
        }
        result = {
            "engine_version": APP_VERSION, "created_at": datetime.now().isoformat(timespec="seconds"),
            "llm_provider": "ollama-local", "ollama_url": base_url, "model": model, "visual_check_used": bool(use_visual), "vlm": vlm_stats,
            "old_document": old_meta, "new_document": new_meta, "foreword": foreword,
            "metrics": struct["metrics"], "classification_stats": cls["stats"],
            "analysis": {"items": items_out, "editorial": editorial, "systematic_pairs": struct["metrics"]["hunks"].get("systematic_pairs", []),
                         "undeclared_discarded_count": len(undeclared_ids), "undeclared_discarded_ids": undeclared_ids,
                         "fragment_groups": frags, "visual_checks": visual, "warnings": warnings_,
                         "all_hunks": records},
            "alignment_summary": alignment_summary,
            "highlight_stats": hl_stats, "highlighted_old_pdf": str(old_hl), "highlighted_new_pdf": str(new_hl),
            "page_images": page_images,
            "architecture": {
                "foreword": "page-1-forward literal FOREWORD text search -> sequential text LLM boundary judgment",
                "structure": "running header/footer removal (position+repetition), TOC detection, language per page, "
                             "Directives numbering + typography/TOC headings with TOC-grounded sequential validation, ISO 10241-1 entries",
                "alignment": "sections: number+title -> title -> calibrated TF-IDF cosine; paragraphs: Gale-Church DP with 1-2/2-1 beads, threshold calibrated per pair (Otsu)",
                "diff": "token-level Ratcliff/Obershelp opcodes; rule tags: editorial, renumber (learned maps), verbal form, fragment",
                "llm": "region-only candidates (no code filter on change type / paragraph kind); batched judgement per hunk; section-context pass for every request; full read-through for unlocated items",
                "vlm": "optional, fragment sections only",
                "report": "boxes coloured per FOREWORD item with the report's change label in the margin, popup notes, "
                          "adjacent boxes merged, fragment boxes widened to the drawing they sit in, legend page; "
                          "HTML shows original-case diff text, Korean names for types/kinds/metrics, printed page numbers; "
                          "per-change page-image viewer (only that change's boxes, word runs, insertion band); "
                          "SYSTEMATIC class for document-wide recurring replacements; open items need meaning_changed",
            },
        }
        emit(96, "HTML/JSON 저장")
        json_out = out_dir / f"IEC_revision_v7_0_{stamp}.json"
        html_out = out_dir / f"IEC_revision_v7_0_{stamp}.html"
        result["json_out"], result["html_out"] = str(json_out), str(html_out)
        elapsed = time.perf_counter() - started
        result["timing"] = {"elapsed_seconds": round(elapsed, 2), "elapsed_hms": format_elapsed(elapsed)}
        html_out.write_text(report_html(result, old_hl, new_hl, out_dir), encoding="utf-8")
        json_out.write_text(json.dumps(result, ensure_ascii=False, indent=2, default=str), encoding="utf-8")
        emit(100, f"완료 · {result['timing']['elapsed_hms']}")
        return result
    finally:
        old_doc.close()
        new_doc.close()


def _progress_fraction(msg: str) -> float:
    m = re.search(r"(\d+)/(\d+)", msg)
    if not m:
        return 0.0
    a, b = int(m.group(1)), int(m.group(2))
    return min(1.0, a / b) if b else 0.0


def run_pipeline(old_path: Path, new_path: Path, base_url: str, model: str, use_visual: bool = False, progress=None,
                 cross_check: bool = False) -> dict:
    global _ACTIVE_LOG_PATH
    run_stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = new_path.parent / f"IEC_revision_v7_0_{run_stamp}.log"
    _ACTIVE_LOG_PATH = log_path
    started = time.perf_counter()
    outcome = "error"
    _log_event("RUN_START", app_version=APP_VERSION, old_pdf=str(old_path), new_pdf=str(new_path), model=model,
               ollama_url=base_url, visual=bool(use_visual), cross_check=bool(cross_check), log_path=str(log_path))
    try:
        result = _run_pipeline_impl(old_path, new_path, base_url, model, use_visual, progress=progress, cross_check=cross_check)
        result["debug_log"] = str(log_path)
        outcome = "success"
        _log_event("RUN_SUCCESS", elapsed_seconds=round(time.perf_counter() - started, 3), json_out=result.get("json_out"))
        return result
    except Exception as e:
        _log_event("RUN_ERROR", elapsed_seconds=round(time.perf_counter() - started, 3), error_type=type(e).__name__,
                   error=str(e), traceback=traceback.format_exc())
        raise RuntimeError(f"{e}\n디버그 로그: {log_path}") from e
    finally:
        _log_event("RUN_END", outcome=outcome, elapsed_seconds=round(time.perf_counter() - started, 3))
        _ACTIVE_LOG_PATH = None


# ============================================================

# ============================================================

class App:
    BG, SURFACE, TEXT, MUTED, LINE, DARK, BLUE = "#F3F5F7", "#FFFFFF", "#111318", "#6D737C", "#E3E6EA", "#0B0D10", "#2F6FED"

    def __init__(self, root):
        self.root = root
        root.title("IEC Revision Analyzer V7.0 - Hybrid structural diff")
        root.geometry("1480x900")
        root.minsize(1150, 700)
        root.configure(bg=self.BG)
        self.old_var, self.new_var = tk.StringVar(), tk.StringVar()
        self.url_var = tk.StringVar(value=OLLAMA_DEFAULT_URL)
        self.model_var = tk.StringVar(value="")
        self.visual_var = tk.BooleanVar(value=False)
        self.cross_var = tk.BooleanVar(value=False)
        self.status_var = tk.StringVar(value="Ready")
        self.progress_var = tk.DoubleVar(value=0)
        self.elapsed_var = tk.StringVar(value="00:00")
        self.queue = queue.Queue()
        self.worker = None
        self.started_at = None
        self.result = None
        self._styles()
        self._build()
        root.after(400, self.refresh_models)
        root.after(150, self._poll)

    def _styles(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Primary.TButton", background=self.DARK, foreground="white", padding=(15, 10), borderwidth=0)
        style.configure("Secondary.TButton", background="white", foreground=self.TEXT, padding=(12, 9), borderwidth=1)
        style.configure("IEC.Horizontal.TProgressbar", troughcolor="#E8EBEF", background=self.BLUE, thickness=8)

    def _build(self):
        header = tk.Frame(self.root, bg=self.DARK, height=66)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(header, text="IEC REVISION · V7.0 HYBRID", bg=self.DARK, fg="white", font=("Segoe UI", 13, "bold")).pack(side="left", padx=24, pady=20)
        tk.Label(header, text="FOREWORD-FIRST · STRUCTURAL DIFF · LLM JUDGEMENT", bg=self.DARK, fg="#8D98A6", font=("Segoe UI", 9, "bold")).pack(side="left")
        body = tk.Frame(self.root, bg=self.BG)
        body.pack(fill="both", expand=True, padx=30, pady=24)
        body.grid_columnconfigure(0, weight=1, minsize=500)
        body.grid_columnconfigure(1, weight=1, minsize=560)
        body.grid_rowconfigure(0, weight=1)
        left = tk.Frame(body, bg=self.SURFACE, highlightbackground=self.LINE, highlightthickness=1)
        right = tk.Frame(body, bg=self.SURFACE, highlightbackground=self.LINE, highlightthickness=1)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        right.grid(row=0, column=1, sticky="nsew", padx=(10, 0))
        tk.Label(left, text="Revision analysis", bg=self.SURFACE, fg=self.TEXT, font=("Segoe UI", 22, "bold")).pack(anchor="w", padx=24, pady=(24, 4))
        tk.Label(left, text="CODE가 두 판의 구조를 정렬해 모든 차이를 찾고, LLM은 FOREWORD 기준으로 의미 변화만 판정합니다.",
                 bg=self.SURFACE, fg=self.MUTED, wraplength=500, justify="left", font=("Malgun Gothic", 10)).pack(anchor="w", padx=24, pady=(0, 22))
        self._file_row(left, "OLD IEC PDF", self.old_var, self.choose_old)
        self._file_row(left, "NEW IEC PDF", self.new_var, self.choose_new)
        form = tk.Frame(left, bg=self.SURFACE)
        form.pack(fill="x", padx=24, pady=(18, 0))
        tk.Label(form, text="Ollama URL", bg=self.SURFACE, fg=self.MUTED).grid(row=0, column=0, sticky="w")
        tk.Entry(form, textvariable=self.url_var).grid(row=1, column=0, sticky="ew", pady=(4, 12))
        tk.Label(form, text="Model", bg=self.SURFACE, fg=self.MUTED).grid(row=2, column=0, sticky="w")
        self.model_combo = ttk.Combobox(form, textvariable=self.model_var, state="readonly")
        self.model_combo.grid(row=3, column=0, sticky="ew", pady=(4, 12))
        form.grid_columnconfigure(0, weight=1)
        tk.Checkbutton(left, text=f"수식·그림 VLM 비교 ({VLM_MODEL}, FOREWORD 영역 안의 조각만)", variable=self.visual_var, bg=self.SURFACE, fg=self.TEXT,
                       activebackground=self.SURFACE, selectcolor=self.SURFACE, font=("Malgun Gothic", 10)).pack(anchor="w", padx=24, pady=(4, 2))
        tk.Checkbutton(left, text="1차 선별 교차 검증 (두 번 판정, 불일치는 맥락 재판정 · 시간 약 1.5배)", variable=self.cross_var,
                       bg=self.SURFACE, fg=self.TEXT, activebackground=self.SURFACE, selectcolor=self.SURFACE,
                       font=("Malgun Gothic", 10)).pack(anchor="w", padx=24, pady=(0, 14))
        self.run_btn = ttk.Button(left, text="분석 시작", style="Primary.TButton", command=self.start)
        self.run_btn.pack(fill="x", padx=24, pady=(0, 10))
        prog = tk.Frame(left, bg=self.SURFACE)
        prog.pack(fill="x", padx=24, pady=(10, 22))
        self.progress = ttk.Progressbar(prog, variable=self.progress_var, maximum=100, style="IEC.Horizontal.TProgressbar")
        self.progress.pack(fill="x")
        line = tk.Frame(prog, bg=self.SURFACE)
        line.pack(fill="x", pady=(7, 0))
        tk.Label(line, textvariable=self.status_var, bg=self.SURFACE, fg=self.MUTED, wraplength=410, justify="left").pack(side="left", fill="x", expand=True)
        tk.Label(line, textvariable=self.elapsed_var, bg=self.SURFACE, fg=self.MUTED).pack(side="right")
        tk.Label(right, text="Result", bg=self.SURFACE, fg=self.TEXT, font=("Segoe UI", 22, "bold")).pack(anchor="w", padx=24, pady=(24, 8))
        self.result_text = tk.Text(right, wrap="word", bd=0, bg="#FAFBFC", fg=self.TEXT, padx=14, pady=14, font=("Malgun Gothic", 10))
        self.result_text.pack(fill="both", expand=True, padx=24, pady=(0, 12))
        buttons = tk.Frame(right, bg=self.SURFACE)
        buttons.pack(fill="x", padx=24, pady=(0, 22))
        self.html_btn = ttk.Button(buttons, text="HTML 열기", style="Secondary.TButton", command=self.open_html, state="disabled")
        self.html_btn.pack(side="left")
        self.old_btn = ttk.Button(buttons, text="OLD PDF", style="Secondary.TButton", command=self.open_old, state="disabled")
        self.old_btn.pack(side="left", padx=8)
        self.new_btn = ttk.Button(buttons, text="NEW PDF", style="Secondary.TButton", command=self.open_new, state="disabled")
        self.new_btn.pack(side="left")

    def _file_row(self, parent, label, var, cmd):
        frame = tk.Frame(parent, bg=self.SURFACE)
        frame.pack(fill="x", padx=24, pady=6)
        tk.Label(frame, text=label, bg=self.SURFACE, fg=self.MUTED).pack(anchor="w")
        row = tk.Frame(frame, bg=self.SURFACE)
        row.pack(fill="x", pady=(4, 0))
        tk.Entry(row, textvariable=var).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="선택", style="Secondary.TButton", command=cmd).pack(side="left", padx=(8, 0))

    def choose_old(self):
        p = filedialog.askopenfilename(filetypes=[("PDF", "*.pdf")])
        if p:
            self.old_var.set(p)

    def choose_new(self):
        p = filedialog.askopenfilename(filetypes=[("PDF", "*.pdf")])
        if p:
            self.new_var.set(p)

    def refresh_models(self):
        try:
            names = ollama_list_models(self.url_var.get())
            self.model_combo["values"] = names
            if names and not self.model_var.get():
                self.model_var.set(next((x for x in names if "qwen3.8:27b" in x), names[0]))
        except Exception as e:
            self.status_var.set(str(e))

    def start(self):
        if self.worker and self.worker.is_alive():
            return
        old = Path(self.old_var.get().strip().strip('"'))
        new = Path(self.new_var.get().strip().strip('"'))
        model = self.model_var.get()
        if not self.old_var.get().strip() or not self.new_var.get().strip() or not old.is_file() or not new.is_file():
            messagebox.showerror("오류", "OLD/NEW PDF 파일을 선택하세요.")
            return
        if old.resolve() == new.resolve():
            messagebox.showerror("오류", "OLD와 NEW에 같은 PDF가 선택되었습니다.")
            return
        if not model:
            messagebox.showerror("오류", "Ollama model을 선택하세요.")
            return
        self.progress_var.set(0)
        self.status_var.set("시작")
        self.result_text.delete("1.0", "end")
        for b in (self.run_btn, self.html_btn, self.old_btn, self.new_btn):
            b.configure(state="disabled")
        self.started_at = time.perf_counter()

        def worker():
            try:
                res = run_pipeline(old, new, self.url_var.get(), model, bool(self.visual_var.get()),
                                   progress=lambda m_: self.queue.put(("progress", m_)),
                                   cross_check=bool(self.cross_var.get()))
                self.queue.put(("done", res))
            except Exception:
                self.queue.put(("error", traceback.format_exc()))

        self.worker = threading.Thread(target=worker, daemon=True)
        self.worker.start()

    def _poll(self):
        try:
            while True:
                kind, payload = self.queue.get_nowait()
                if kind == "progress":
                    self.status_var.set(payload)
                    m_ = re.match(r"\[\s*(\d+)%\]", payload)
                    if m_:
                        self.progress_var.set(int(m_.group(1)))
                elif kind == "done":
                    self.result = payload
                    self.progress_var.set(100)
                    self.status_var.set("완료")
                    for b in (self.run_btn, self.html_btn, self.old_btn, self.new_btn):
                        b.configure(state="normal")
                    self._show_result(payload)
                elif kind == "error":
                    self.run_btn.configure(state="normal")
                    self.status_var.set("오류")
                    self.result_text.insert("end", payload)
                    messagebox.showerror("분석 오류", payload.splitlines()[-1] if payload.splitlines() else payload)
        except queue.Empty:
            pass
        if self.started_at and self.worker and self.worker.is_alive():
            self.elapsed_var.set(format_elapsed(time.perf_counter() - self.started_at))
        self.root.after(150, self._poll)

    def _show_result(self, res: dict):
        self.result_text.delete("1.0", "end")
        a = res["analysis"]
        self.result_text.insert("end", f"완료 시간: {res['timing']['elapsed_hms']}\n")
        if res.get("debug_log"):
            self.result_text.insert("end", f"디버그 로그: {res['debug_log']}\n")
        self.result_text.insert("end", f"FOREWORD 항목 {len(a['items'])}건 · 배정된 내용 변경 {sum(len(i['changes']) for i in a['items'])}건 · 편집상 {len(a['editorial'])}건 · 수식·표·그림 조각 묶음 {len(a['fragment_groups'])}개 절 · 미선언(제외) {a.get('undeclared_discarded_count', 0)}건\n")
        for w in a["warnings"]:
            self.result_text.insert("end", f"경고: {w}\n")
        self.result_text.insert("end", "\n")
        for it in a["items"]:
            self.result_text.insert("end", f"[{it['marker']}] {it['action']} · {it['severity']} · {it['title_ko']}\n{it['summary_ko']}\n")
            for ch in it["changes"][:12]:
                self.result_text.insert("end", f"  - {ch.get('title_ko','')} ({ch.get('new_location') or ch.get('old_location')})\n")
            if len(it["changes"]) > 12:
                self.result_text.insert("end", f"  … 외 {len(it['changes']) - 12}건 (HTML 참조)\n")
            self.result_text.insert("end", "\n")

    def _open_path(self, key):
        if self.result and self.result.get(key):
            webbrowser.open(Path(self.result[key]).resolve().as_uri())

    def open_html(self):
        self._open_path("html_out")

    def open_old(self):
        self._open_path("highlighted_old_pdf")

    def open_new(self):
        self._open_path("highlighted_new_pdf")


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
