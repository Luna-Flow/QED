#!/usr/bin/env python3
"""Check that the tracked Lean rules and laws have MoonBit tests.

A MoonBit test covers the Lean name `N` when its name starts with `N:`. Two
kinds of names are tracked:

- every constructor `I.C` of the inductives in TRACKED_INDUCTIVES; one the
  MoonBit code does not implement is listed in NOT_IMPLEMENTED with the reason;
- the theorems in TRACKED_THEOREMS, which must exist in the Lean sources.

The check fails closed: an uncovered name, a stale NOT_IMPLEMENTED entry, a
tracked theorem missing from Lean, and a test whose prefix looks like a Lean
name but is not tracked (usually a typo) are all errors. This is a coverage
check over test names; it establishes no correspondence theorem.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from qed_obligations import lean_source_without_comments_and_strings


ROOT = Path(__file__).resolve().parents[1]
HOL = ROOT / "formal_verification/QEDFV/HOL"
SRC = ROOT / "src"

TRACKED_INDUCTIVES = ("Derivation",)

TRACKED_THEOREMS = (
    "Ty.subst_id",
    "Ty.subst_comp",
    "Ty.subst_congr",
    "Ty.IsInst.refl",
    "Ty.IsInst.inst",
    "Term.erase_inj",
    "Term.erase_instType",
    "Term.instType_var",
    "Term.instType_instType",
    "Term.instType_congr",
    "Term.instType_single",
    "Term.substitute_var",
    "Term.substitute_substitute",
    "Term.substitute_instType",
)

NOT_IMPLEMENTED: dict[str, str] = {
    "Derivation.chooseWitness": "src/logic has no derived Hilbert-choice rule yet",
    "Derivation.chooseHyp": "src/logic has no derived Hilbert-choice rule yet",
    "Derivation.indInfinity": "the kernel has no infinity axiom; "
                              "ks_register_ind_infinity_axiom only records an already-proved anchor",
    "Derivation.allIntro": "src/logic has no quantifier prelude yet",
    "Derivation.allElim": "src/logic has no quantifier prelude yet",
    "Derivation.exIntro": "src/logic has no quantifier prelude yet",
    "Derivation.exElim": "src/logic has no quantifier prelude yet",
    "Derivation.classical": "src/logic has no derived classical rule yet",
}

DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|namespace|end|section)\b",
    re.MULTILINE,
)
CONSTRUCTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)
THEOREM = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)", re.MULTILINE)
# A test prefix that looks like a qualified Lean name: `Ty.subst_id:`.
TEST_NAME = re.compile(r'^\s*(?:async\s+)?test\s+"([A-Z][A-Za-z0-9_\']*(?:\.[A-Za-z0-9_\']+)+):',
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
    return [f"{inductive}.{name}" for name in names]


def theorems(source: str) -> set[str]:
    return set(THEOREM.findall(lean_source_without_comments_and_strings(source)))


def tested(test_sources: list[str]) -> set[str]:
    return {name for source in test_sources for name in TEST_NAME.findall(source)}


def check(required: list[str], tests: set[str], not_implemented: dict[str, str]) -> list[str]:
    errors = []
    for name in required:
        if name in tests and name in not_implemented:
            errors.append(f"{name}: tested but listed as not implemented")
        elif name not in tests and name not in not_implemented:
            errors.append(f"{name}: no MoonBit test")
    for name in sorted(tests - set(required)):
        errors.append(f"{name}: test names an untracked Lean name")
    for name in sorted(set(not_implemented) - set(required)):
        errors.append(f"{name}: stale NOT_IMPLEMENTED entry")
    return errors


def main() -> int:
    try:
        lean = {path: path.read_text(encoding="utf-8") for path in sorted(HOL.rglob("*.lean"))}
        required: list[str] = []
        for inductive in TRACKED_INDUCTIVES:
            found = [constructors(text, inductive) for text in lean.values()
                     if re.search(rf"^inductive\s+{re.escape(inductive)}\b", text, re.MULTILINE)]
            if len(found) != 1:
                raise ValueError(f"inductive {inductive}: expected one definition, found {len(found)}")
            required += found[0]
        declared = set().union(*(theorems(text) for text in lean.values()))
        missing = [name for name in TRACKED_THEOREMS if name not in declared]
        if missing:
            raise ValueError(f"tracked theorems not found in Lean: {', '.join(missing)}")
        required += TRACKED_THEOREMS
        sources = [path.read_text(encoding="utf-8") for path in sorted(SRC.rglob("*.mbt"))
                   if path.name.endswith(("_test.mbt", "_wbtest.mbt"))]
        errors = check(required, tested(sources), NOT_IMPLEMENTED)
        if errors:
            raise ValueError("\n  " + "\n  ".join(errors))
        print(f"Lean conformance coverage: {len(required) - len(NOT_IMPLEMENTED)}/{len(required)} "
              f"tracked rules and laws tested, {len(NOT_IMPLEMENTED)} not implemented in MoonBit")
        return 0
    except (ValueError, OSError) as error:
        print(f"Lean conformance coverage failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
