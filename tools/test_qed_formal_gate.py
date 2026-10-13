"""Regression cases for a verification gate that must fail closed."""

import unittest

from qed_formal_gate import check_audit, check_source


class FormalGateTests(unittest.TestCase):
    def test_standard_foundations_and_axiom_free_result(self):
        found = check_audit(
            "'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'B' does not depend on any axioms\n", ["A", "B"])
        self.assertEqual(found["B"], [])

    def test_missing_or_unparsed_output_is_rejected(self):
        for output in ("", "'A' has an unrecognized dependency report\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                check_audit(output, ["A"])

    def test_hidden_project_axiom_and_sorry_are_rejected(self):
        for axiom in ("sorryAx", "Project.assumedSoundness"):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                check_audit(f"'A' depends on axioms: [{axiom}]\n", ["A"])

    def test_duplicate_extra_and_empty_audits_are_rejected(self):
        result = "'A' does not depend on any axioms\n"
        for output, expected in ((result * 2, ["A"]), (result, ["B"]),
                                 (result, []), (result, ["A", "A"])):
            with self.subTest(output=output, expected=expected), self.assertRaises(ValueError):
                check_audit(output, expected)

    def test_admissions_and_project_axioms_are_rejected(self):
        for source in ("theorem p : True := by sorry", "theorem p : True := by admit",
                       "namespace N\naxiom p : False\nend N"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                check_source(source, "test.lean")

    def test_comments_and_strings_are_not_proof_admissions(self):
        check_source('/- axiom /- sorry -/ admit -/\n-- sorry\ndef s := "axiom sorry admit"',
                     "test.lean")


if __name__ == "__main__":
    unittest.main()
