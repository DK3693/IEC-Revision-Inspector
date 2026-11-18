"""Document-free checks using fictitious data; no model or private corpus required."""
import unittest
from pathlib import Path
from src import analyzer as a

class PublicCoreTests(unittest.TestCase):
    def test_two_paragraphs_can_align_to_one(self):
        left = [a.Paragraph('body', 'Record the measured value.', []),
                a.Paragraph('body', 'Include the selected condition.', [])]
        right = [a.Paragraph('body', 'Record the measured value. Include the selected condition.', [])]
        beads = a.align_paragraphs(left, right, threshold=0.4)
        self.assertEqual(len(beads), 1)
        self.assertEqual(beads[0][0], [0, 1])
        self.assertEqual(beads[0][1], [0])

    def test_renumbered_section_retains_correspondence(self):
        old = a.Section('OLD','4','Example procedure',1,'clause')
        new = a.Section('NEW','5','Example procedure',1,'clause')
        old.paragraphs = [a.Paragraph('body','Record the example test result.',[])]
        new.paragraphs = [a.Paragraph('body','Record the example test result.',[])]
        result = a.align_sections([old],[new])
        self.assertEqual(len(result['pairs']),1)
        self.assertEqual(result['deleted'],[])
        self.assertEqual(result['added'],[])

    def test_export_links_are_portable(self):
        folder = Path.cwd() / 'public-demo'
        href = a._pdf_href(folder / 'sample new.pdf',folder,7)
        self.assertNotIn('file:',href)
        self.assertNotIn(str(Path.cwd()),href)
        self.assertTrue(href.endswith('#page=7'))

    def test_evidence_boxes_preserve_page_boundary(self):
        lines=[a.Line('NEW',p,1,1,'Fictitious evidence',(10,20,100,40),10,False,0.1,800) for p in (2,3)]
        anchors=a.Paragraph('body','Fictitious evidence',lines).anchors()
        self.assertEqual([x['page'] for x in anchors],[2,3])
        self.assertEqual(anchors[0]['bbox'],[10,20,100,40])

if __name__ == '__main__':
    unittest.main()
