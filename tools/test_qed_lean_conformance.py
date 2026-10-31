"""Regression cases for the Lean-to-MoonBit test coverage check."""

import unittest

from qed_lean_conformance import check, constructors, covered


LEAN = """
inductive D : Nat → Prop where
  | a : D 0
  | /-- doc -/ b (n : Nat) : D n → D (n + 1)
  -- | c : commented out
  | c' : D 7

theorem t : D 0 := .a
"""


class LeanConformanceTests(unittest.TestCase):
    def test_constructors_skip_comments_and_stop_at_next_declaration(self):
        self.assertEqual(constructors(LEAN, "D"), ["a", "b", "c'"])

    def test_missing_inductive_is_rejected(self):
        with self.assertRaises(ValueError):
            constructors(LEAN, "E")

    def test_test_names_are_collected(self):
        found = covered(['test "D.a: x" {\n}\n', 'async test "D.b: y" {}', 'test "other" {}'])
        self.assertEqual(found, {"D": {"a", "b"}})

    def test_complete_coverage_passes(self):
        self.assertEqual(check({"D": ["a", "b"]}, {"D": {"a"}}, {"D": {"b": "why"}}), [])

    def test_uncovered_unknown_and_stale_entries_fail(self):
        cases = (
            ({"D": {"a"}}, {}),                         # b uncovered
            ({"D": {"a", "b", "z"}}, {}),               # unknown test
            ({"D": {"a", "b"}}, {"D": {"b": "why"}}),   # tested and skipped
            ({"D": {"a", "b"}}, {"D": {"q": "why"}}),   # stale entry
            ({"D": {"a", "b"}}, {"E": {"q": "why"}}),   # untracked inductive
        )
        for tests, skipped in cases:
            with self.subTest(tests=tests, skipped=skipped):
                self.assertTrue(check({"D": ["a", "b"]}, tests, skipped))


if __name__ == "__main__":
    unittest.main()
