#!/usr/bin/env python3
"""Build the Lean theory and check the explicitly selected foundation audit.

The lexical source check is a hygiene check, not a Lean parser. The authoritative
dependency evidence comes from elaborating AxiomAudit.lean with the pinned Lean
toolchain. This gate establishes no MoonBit correspondence theorem.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

from qed_obligations import lean_source_without_comments_and_strings


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal_verification"
AUDIT = FORMAL / "QEDFV/HOL/AxiomAudit.lean"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AUDIT_COMMAND = re.compile(r"^\s*#print\s+axioms\s+(\S+)\s*$", re.MULTILINE)
AUDIT_RESULT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)$",
    re.MULTILINE,
)


def check_source(source: str, label: str) -> None:
    code = lean_source_without_comments_and_strings(source)
    forbidden = re.search(r"\b(?:sorry|admit|axiom)\b", code)
    if forbidden:
        line = code.count("\n", 0, forbidden.start()) + 1
        raise ValueError(f"{label}:{line}: forbidden proof admission or project axiom: {forbidden[0]}")


def check_audit(output: str, expected: list[str]) -> dict[str, list[str]]:
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("the audit must select a nonempty, duplicate-free list of declarations")
    found: dict[str, list[str]] = {}
    for name, axioms in AUDIT_RESULT.findall(output):
        if name in found:
            raise ValueError(f"duplicate dependency report for {name}")
        dependencies = [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
        unexpected = set(dependencies) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"{name}: unapproved axioms: {', '.join(sorted(unexpected))}")
        found[name] = dependencies
    if set(found) != set(expected):
        missing = sorted(set(expected) - set(found))
        extra = sorted(set(found) - set(expected))
        raise ValueError(f"audit coverage mismatch: missing={missing}, unexpected={extra}")
    return found


def main() -> int:
    try:
        sources = [FORMAL / "QEDFV.lean", *sorted((FORMAL / "QEDFV").rglob("*.lean"))]
        for path in sources:
            check_source(path.read_text(encoding="utf-8"), str(path.relative_to(ROOT)))
        audit_source = lean_source_without_comments_and_strings(AUDIT.read_text(encoding="utf-8"))
        expected = AUDIT_COMMAND.findall(audit_source)
        subprocess.run(["lake", "build"], cwd=FORMAL, check=True)
        result = subprocess.run(
            ["lake", "env", "lean", str(AUDIT.relative_to(FORMAL))],
            cwd=FORMAL, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        print(result.stdout, end="")
        if result.returncode:
            raise ValueError(f"Lean axiom audit failed (exit {result.returncode})")
        found = check_audit(result.stdout, expected)
        print(f"Formal gate passed: {len(sources)} source files; {len(found)} audited declarations; "
              "only propext, Classical.choice, Quot.sound permitted.")
        return 0
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"Formal gate failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
