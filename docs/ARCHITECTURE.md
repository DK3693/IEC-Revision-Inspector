# Architecture

## Design objective

Connect declared technical revisions to verifiable OLD/NEW evidence. The document's FOREWORD defines the review agenda; structural comparison locates candidate evidence; local model inference supplies interpretation.

## Component responsibilities

| Component | Responsibility | Output |
|---|---|---|
| Extraction | Read page text, typography, line/word geometry and ruled tables | Coordinate-bearing lines and cell grids |
| Normalization | Identify repeated page furniture, contents pages and language segments; conservatively join broken words | Logical text with provenance |
| Structure | Recognize numbered clauses, annexes, definitions, notes and source statements | Section hierarchy |
| Alignment | Combine number/title anchors, TF-IDF body similarity and child agreement; align paragraphs with split/merge support | OLD/NEW correspondences |
| Change representation | Generate text, heading, table, relocation and insertion/deletion candidates | Hunks with geometry |
| FOREWORD interpretation | Extract declarations and derive item-specific regions and evidence criteria | Dynamic item specifications |
| Confirmation | Evaluate candidates, read context and requested references, optionally compare visual crops | Item association and explanation inputs |
| Presentation | Group confirmed hunks, generate explanations, render reports and annotations | Reviewable evidence packages |

## Evidence model

```text
Line -> Paragraph -> Section -> Matched section pair -> Hunk -> Change group -> FOREWORD item
  \_______________ page and bounding-box provenance _______________/
```

Line records preserve physical page numbers, text, typography and bounding boxes. Paragraphs aggregate line anchors. Hunks retain both source sides, change operations and locations. Change groups collect related hunks within an item and clause pair; report labels are shared with PDF annotations.

The model does not invent page coordinates. Addition and deletion records can show an insertion/deletion boundary inferred from neighbouring aligned content. The viewer distinguishes these boundary indications from observed text evidence.

## Matching and inference

Section matching progresses from explicit structural anchors to text similarity and child-supported container alignment. Paragraph matching allows one-to-one, one-to-two and two-to-one relationships so changes in PDF block segmentation need not become unrelated additions and deletions. Table comparison uses extracted cell grids and geometry.

Model requests use JSON response schemas and bounded batches. Candidate confirmation, contextual reading, grouped explanation and item summarization have distinct input/output responsibilities. Optional cross-checking repeats candidate decisions with different batches and sends disagreements for contextual review. Optional visual comparison is restricted to selected document regions.

## Application and exports

The Tkinter application exposes file selection, local model selection, analysis options, progress and output navigation. Background work communicates with the UI through a queue. The HTML report includes grouped change cards and an image-backed evidence viewer; the annotated PDFs carry the same item colours and change identifiers.

A portable output package contains HTML, two annotated PDFs and the generated page-image folder. JSON provides structured data for downstream integrations. Runtime outputs remain outside this public source snapshot.
