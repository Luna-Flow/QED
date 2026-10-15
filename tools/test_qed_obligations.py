"""Protect authored compliance content while refreshing the obligation matrix."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import qed_obligations as obligations


class ComplianceDocumentTests(unittest.TestCase):
    def update(self, document: str, generated: str = "new matrix\n") -> str:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "conformance.md"
            output.write_text(document, encoding="utf-8")
            with patch.object(obligations, "OUTPUT", output):
                return obligations.update_document(generated)

    def test_refresh_preserves_authored_content_and_is_idempotent(self):
        prefix = "# Review\n\nHandwritten evidence.\n\n"
        suffix = "\n\n## Follow-up\n\nKeep this text.\n"
        document = prefix + obligations.BEGIN_MARKER + "\nold matrix\n" + obligations.END_MARKER + suffix
        updated = self.update(document)
        self.assertEqual(updated, prefix + obligations.BEGIN_MARKER + "\n\nnew matrix\n\n" + obligations.END_MARKER + suffix)
        self.assertEqual(self.update(updated), updated)

    def test_invalid_markers_reject_refresh(self):
        begin, end = obligations.BEGIN_MARKER, obligations.END_MARKER
        for document in ("# Review\n", begin, end, end + begin, begin + begin + end, begin + end + end):
            with self.subTest(document=document), self.assertRaises(ValueError):
                self.update(document)


if __name__ == "__main__":
    unittest.main()
