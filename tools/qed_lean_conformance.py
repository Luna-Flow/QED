#!/usr/bin/env python3
"""Check that every constructor of the tracked Lean inductives has MoonBit tests.

A MoonBit test covers constructor `C` of inductive `I` when its name starts with
`I.C:`. A constructor the MoonBit code does not implement must be listed in
NOT_IMPLEMENTED with the reason. The check fails closed: an uncovered
constructor, a test naming an unknown constructor, and a stale NOT_IMPLEMENTED
entry are all errors. This is a coverage check over test names; it establishes
no correspondence theorem.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from qed_obligations import lean_source_without_comments_and_strings


ROOT = Path(__file__).resolve().parents[1]
HOL = ROOT / "formal_verification/QEDFV/HOL"
SRC = ROOT / "src"

# (Lean file, inductive name) pairs whose constructors need MoonBit tests.
TRACKED = (
    (HOL / "Derivation.lean", "Derivation"),
)

NOT_IMPLEMENTED: dict[str, dict[str, str]] = {
    "Derivation": {
        "chooseWitness": "src/logic has no derived Hilbert-choice rule yet",
        "chooseHyp": "src/logic has no derived Hilbert-choice rule yet",
        "indInfinity": "the kernel has no infinity axiom; "
                       "ks_register_ind_infinity_axiom only records an already-proved anchor",
        "allIntro": "src/logic has no quantifier prelude yet",
        "allElim": "src/logic has no quantifier prelude yet",
        "exIntro": "src/logic has no quantifier prelude yet",
        "exElim": "src/logic has no quantifier prelude yet",
        "classical": "src/logic has no derived classical rule yet",
    },
}

DECLARATION = re.compile(
    r"^(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|namespace|end|section)\b",
    re.MULTILINE,
)
CONSTRUCTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)
TEST_NAME = re.compile(r'^\s*(?:async\s+)?test\s+"([A-Za-z_][A-Za-z0-9_]*)\.([A-Za-z_][A-Za-z0-9_\']*):',
                       re.MULTILINE)


def constructors(source: str, inductive: str) -> list[str]:
    code = lean_source_without_comments_and_strings(source)
    start = re.search(rf"^inductive\s+{re.escape(inductive)}\b", code, re.MULTILINE)
    if start is None:
        raise ValueError(f"inductive {inductive} not found")
    body_start = code.index(" where", start.end())
    following = DECLARATION.search(code, body_start)
    body = code[body_start:following.start() if following else len(code)]
    names = CONSTRUCTOR.findall(body)
    if not names or len(set(names)) != len(names):
        raise ValueError(f"inductive {inductive}: empty or duplicate constructor list")
    return names


def covered(test_sources: list[str]) -> dict[str, set[str]]:
    found: dict[str, set[str]] = {}
    for source in test_sources:
        for inductive, constructor in TEST_NAME.findall(source):
            found.setdefault(inductive, set()).add(constructor)
    return found


def check(ctors: dict[str, list[str]], tests: dict[str, set[str]],
          not_implemented: dict[str, dict[str, str]]) -> list[str]:
    errors = []
    for inductive, names in ctors.items():
        tested = tests.get(inductive, set())
        skipped = not_implemented.get(inductive, {})
        for name in names:
            if name in tested and name in skipped:
                errors.append(f"{inductive}.{name}: tested but listed as not implemented")
            elif name not in tested and name not in skipped:
                errors.append(f"{inductive}.{name}: no MoonBit test")
        for name in sorted(tested - set(names)):
            errors.append(f"{inductive}.{name}: test names an unknown constructor")
        for name in sorted(set(skipped) - set(names)):
            errors.append(f"{inductive}.{name}: stale NOT_IMPLEMENTED entry")
    for inductive in sorted(set(not_implemented) - set(ctors)):
        errors.append(f"{inductive}: NOT_IMPLEMENTED for an untracked inductive")
    return errors


def main() -> int:
    try:
        ctors = {name: constructors(path.read_text(encoding="utf-8"), name) for path, name in TRACKED}
        sources = [path.read_text(encoding="utf-8") for path in sorted(SRC.rglob("*_test.mbt"))]
        sources += [path.read_text(encoding="utf-8") for path in sorted(SRC.rglob("*_wbtest.mbt"))]
        tests = covered(sources)
        errors = check(ctors, {k: v for k, v in tests.items() if k in ctors}, NOT_IMPLEMENTED)
        if errors:
            raise ValueError("\n  " + "\n  ".join(errors))
        for inductive, names in ctors.items():
            skipped = len(NOT_IMPLEMENTED.get(inductive, {}))
            print(f"{inductive}: {len(names) - skipped}/{len(names)} constructors tested, "
                  f"{skipped} not implemented in MoonBit")
        return 0
    except (ValueError, OSError) as error:
        print(f"Lean conformance coverage failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
