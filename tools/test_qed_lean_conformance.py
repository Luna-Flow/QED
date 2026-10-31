"""Regression cases for the Lean-to-MoonBit test coverage check."""

import unittest

from qed_lean_conformance import check, constructors, tested, theorems


LEAN = """
inductive D : Nat → Prop where
  | a : D 0
  | /-- doc -/ b (n : Nat) : D n → D (n + 1)
  -- | c : commented out
  | c' : D 7

theorem t : D 0 := .a
@[simp] theorem Ty.subst_id : True := trivial
/- theorem Hidden.law : True := trivial -/
"""


class LeanConformanceTests(unittest.TestCase):
    def test_constructors_skip_comments_and_stop_at_next_declaration(self):
        self.assertEqual(constructors(LEAN, "D"), ["D.a", "D.b", "D.c'"])

    def test_missing_inductive_is_rejected(self):
        with self.assertRaises(ValueError):
            constructors(LEAN, "E")

    def test_theorems_include_attributes_and_skip_comments(self):
        self.assertEqual(theorems(LEAN), {"t", "Ty.subst_id"})

    def test_test_names_are_collected(self):
        found = tested(['test "D.a: x" {\n}\n', 'async test "D.b: y" {}',
                        'test "Ty.IsInst.refl: z" {}', 'test "other: w" {}'])
        self.assertEqual(found, {"D.a", "D.b", "Ty.IsInst.refl"})

    def test_complete_coverage_passes(self):
        self.assertEqual(check(["D.a", "D.b", "T.law"], {"D.a", "T.law"}, {"D.b": "why"}), [])

    def test_uncovered_unknown_and_stale_entries_fail(self):
        cases = (
            ({"D.a"}, {}),                       # D.b uncovered
            ({"D.a", "D.b", "D.z"}, {}),         # untracked name, e.g. a typo
            ({"D.a", "D.b"}, {"D.b": "why"}),    # tested and skipped
            ({"D.a", "D.b"}, {"D.q": "why"}),    # stale entry
        )
        for tests, skipped in cases:
            with self.subTest(tests=tests, skipped=skipped):
                self.assertTrue(check(["D.a", "D.b"], tests, skipped))


if __name__ == "__main__":
    unittest.main()
