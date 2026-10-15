#!/usr/bin/env python3
"""Validate and render QED's proof-obligation registry.

The JSON registry is the source of truth. Source-reference validation checks
exact Lean declarations, including their namespaces; it does not replace a
Lean build or prove the statements of those declarations.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "doc/manual/qed_obligations.json"
OUTPUT = ROOT / "doc/manual/conformance.md"
BEGIN_MARKER = "<!-- BEGIN GENERATED OBLIGATION MATRIX -->"
END_MARKER = "<!-- END GENERATED OBLIGATION MATRIX -->"
STATUSES = (
    "proved-and-refined",
    "proved-abstractly",
    "tested-only",
    "implemented-unverified",
    "partial",
    "not-implemented",
    "known-deviation",
    "not-applicable",
)
DIMENSIONS = ("lean", "moonbit", "refinement", "tests")
REQUIREMENT_LEVELS = ("required", "recommended", "optional")
SEVERITIES = ("critical", "high", "medium", "low", "info")
ID_RE = re.compile(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+\Z")
IDENT = r"(?:«[^»\n]+»|(?:[^\W\d]|_)[\w'!?]*)"
LEAN_NAME = rf"{IDENT}(?:\.{IDENT})*"
LEAN_COMMAND_RE = re.compile(
    rf"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    rf"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    rf"(?:(?P<scope>namespace|section|mutual|end)"
    rf"(?:[ \t]+(?P<scope_name>{LEAN_NAME}))?"
    rf"|(?:def|theorem|lemma|abbrev|opaque|axiom|structure|inductive|class|instance)"
    rf"[ \t]+(?P<declaration>{LEAN_NAME}))(?=[ \t\n(:{{]|$)",
    re.MULTILINE,
)


def read_registry() -> dict:
    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or data.get("schema") != "qed-proof-obligations/v1":
        raise ValueError("unsupported registry schema")
    return data


def check_path(path_text: str) -> Path:
    if not isinstance(path_text, str) or not path_text:
        raise ValueError("evidence paths must be non-empty strings")
    relative = Path(path_text)
    path = (ROOT / relative).resolve()
    if relative.is_absolute() or not path.is_relative_to(ROOT.resolve()):
        raise ValueError(f"evidence path leaves the repository: {path_text}")
    if not path.is_file():
        raise ValueError(f"missing evidence path: {path_text}")
    return path


def lean_source_without_comments_and_strings(source: str) -> str:
    """Blank comments and string literals while preserving line positions.

    Lean block comments nest. A regular expression that removes only the first
    closing delimiter can manufacture a declaration from commented text.
    """
    chars = list(source)
    index = 0
    block_depth = 0
    in_string = False
    in_line_comment = False
    while index < len(chars):
        pair = source[index:index + 2]
        char = source[index]
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
            else:
                chars[index] = " "
        elif block_depth:
            if pair == "/-":
                chars[index:index + 2] = "  "
                block_depth += 1
                index += 1
            elif pair == "-/":
                chars[index:index + 2] = "  "
                block_depth -= 1
                index += 1
            elif char != "\n":
                chars[index] = " "
        elif in_string:
            if char == "\\":
                chars[index] = " "
                if index + 1 < len(chars):
                    index += 1
                    if source[index] != "\n":
                        chars[index] = " "
            elif char == '"':
                chars[index] = " "
                in_string = False
            elif char != "\n":
                chars[index] = " "
        elif pair == "--":
            chars[index:index + 2] = "  "
            in_line_comment = True
            index += 1
        elif pair == "/-":
            chars[index:index + 2] = "  "
            block_depth = 1
            index += 1
        elif char == '"':
            chars[index] = " "
            in_string = True
        index += 1
    if block_depth or in_string:
        raise ValueError("unterminated Lean comment or string literal")
    return "".join(chars)


def lean_declarations(source: str) -> set[str]:
    """Index explicit source declarations and namespace/section scopes.

    Generated names from macros, structure fields and inductive constructors
    are intentionally not inferred from source text.
    """
    source = lean_source_without_comments_and_strings(source)
    namespace: tuple[str, ...] = ()
    scopes: list[tuple[str, str | None, tuple[str, ...]]] = []
    declarations: set[str] = set()
    for match in LEAN_COMMAND_RE.finditer(source):
        name = match.group("declaration")
        if name:
            components = tuple(name.split("."))
            if components[0] == "_root_":
                declarations.add(".".join(components[1:]))
            else:
                declarations.add(".".join((*namespace, *components)))
            continue
        kind = match.group("scope")
        name = match.group("scope_name")
        if kind == "end":
            if not scopes:
                raise ValueError("unmatched Lean end command")
            opened_kind, opened_name, opened_namespace = scopes.pop()
            namespace = opened_namespace
            if name is not None and name != opened_name:
                raise ValueError(f"Lean end {name} does not close {opened_name}")
            if opened_kind == "mutual" and name is not None:
                raise ValueError("named end is not valid for mutual block")
        else:
            scopes.append((kind, name, namespace))
            if kind == "namespace":
                if name is None:
                    raise ValueError("Lean namespace command has no name")
                components = tuple(name.split("."))
                namespace = components[1:] if components[0] == "_root_" else (*namespace, *components)
    if scopes:
        raise ValueError("unclosed Lean namespace, section, or mutual block")
    return declarations


def check_symbol(path_text: str, symbol: str) -> None:
    if not isinstance(symbol, str) or not re.fullmatch(LEAN_NAME, symbol):
        raise ValueError(f"invalid Lean declaration name: {symbol!r}")
    declarations = lean_declarations(check_path(path_text).read_text(encoding="utf-8"))
    requested = symbol.removeprefix("_root_.")
    if requested in declarations:
        return
    matches = {name for name in declarations if name.endswith("." + requested)}
    if len(matches) != 1:
        reason = "ambiguous" if matches else "missing"
        raise ValueError(f"{reason} cited Lean declaration {symbol!r} in {path_text}")


def string_list(item: dict, key: str) -> list[str]:
    value = item.get(key)
    if not isinstance(value, list) or any(not isinstance(entry, str) or not entry.strip() for entry in value):
        raise ValueError(f"{item['id']}: {key} must be a list of non-empty strings")
    return value


def validate(data: dict) -> None:
    obligations = data.get("obligations")
    if not isinstance(obligations, list) or not obligations or any(not isinstance(item, dict) for item in obligations):
        raise ValueError("registry must contain obligation objects")
    ids = [item.get("id") for item in obligations]
    if any(not isinstance(identifier, str) or ID_RE.fullmatch(identifier) is None for identifier in ids):
        raise ValueError("obligation IDs must be uppercase hyphen-separated identifiers")
    if len(set(ids)) != len(ids):
        raise ValueError("obligation IDs must be unique")
    for item in obligations:
        for key in ("category", "normative_statement", "requirement_level", "severity", "spec", "moonbit_api", "lean", "verification", "evidence", "status", "issues", "assumptions", "exclusions"):
            if key not in item:
                raise ValueError(f"{item['id']}: missing field {key}")
        for key in ("category", "normative_statement", "spec_anchor"):
            if not isinstance(item[key], str) or not item[key].strip():
                raise ValueError(f"{item['id']}: {key} must be a non-empty string")
        if item["requirement_level"] not in REQUIREMENT_LEVELS:
            raise ValueError(f"{item['id']}: unknown requirement level {item['requirement_level']!r}")
        if item["severity"] not in SEVERITIES:
            raise ValueError(f"{item['id']}: unknown severity {item['severity']!r}")
        check_path(item["spec"])
        spec_text = Path(ROOT / item["spec"]).read_text(encoding="utf-8")
        if item["spec_anchor"] not in spec_text:
            raise ValueError(f"{item['id']}: missing specification anchor {item['spec_anchor']!r}")
        for key in ("moonbit_api", "evidence"):
            for path in string_list(item, key):
                check_path(path)
        for key in ("verification", "assumptions", "exclusions"):
            string_list(item, key)
        if not isinstance(item["lean"], list):
            raise ValueError(f"{item['id']}: lean must be a list of declaration citations")
        for citation in item["lean"]:
            if not isinstance(citation, dict) or not {"path", "symbol"} <= citation.keys():
                raise ValueError(f"{item['id']}: Lean citations require path and symbol")
            check_symbol(citation["path"], citation["symbol"])
        issues = item["issues"]
        if not isinstance(issues, list) or any(type(issue) is not int or issue <= 0 for issue in issues):
            raise ValueError(f"{item['id']}: issues must be positive integer issue numbers")
        status = item["status"]
        if not isinstance(status, dict) or set(status) != set(DIMENSIONS):
            raise ValueError(f"{item['id']}: status dimensions must be {DIMENSIONS}")
        if any(not isinstance(value, str) or value not in STATUSES for value in status.values()):
            raise ValueError(f"{item['id']}: unknown status value")


def completion(item: dict) -> str:
    if all(value == "not-applicable" for value in item["status"].values()):
        return "not applicable"
    complete = item["status"]["refinement"] == "proved-and-refined" and all(
        value in ("proved-and-refined", "not-applicable")
        for dimension, value in item["status"].items() if dimension != "tests"
    )
    return "complete" if complete else "open"


def summary_table(obligations: list[dict], field: str, title: str) -> list[str]:
    lines = [f"### {title}", "", "| Group | Total | Complete | Not applicable | Open |", "| --- | ---: | ---: | ---: | ---: |"]
    groups = sorted({item[field] for item in obligations})
    if field == "severity":
        groups = [severity for severity in SEVERITIES if severity in groups]
    elif field == "requirement_level":
        groups = [level for level in REQUIREMENT_LEVELS if level in groups]
    for group in groups:
        selected = [item for item in obligations if item[field] == group]
        counts = Counter(completion(item) for item in selected)
        lines.append(f"| {group} | {len(selected)} | {counts['complete']} | {counts['not applicable']} | {counts['open']} |")
    return lines


def render(data: dict) -> str:
    obligations = data["obligations"]
    counts = {dimension: Counter(item["status"][dimension] for item in obligations) for dimension in DIMENSIONS}
    totals = Counter(completion(item) for item in obligations)
    lines = [
        "## Proof-obligation matrix", "",
        "Generated from [`qed_obligations.json`](qed_obligations.json). The dimensions are independent: a Lean proof does not certify the MoonBit implementation, and tests do not establish refinement.", "",
        "A checked checklist item requires `proved-and-refined` in the refinement dimension. Open means an applicable obligation lacks checked implementation refinement; it does not mean a soundness defect has been demonstrated. Severity records the impact if the obligation is unsatisfied.", "",
        f"Total: **{len(obligations)}**; complete: **{totals['complete']}**; not applicable: **{totals['not applicable']}**; open: **{totals['open']}**.", "",
        "### Status Counts", "",
        "| Dimension | " + " | ".join(status.replace("-", " ") for status in STATUSES) + " |",
        "| --- | " + " | ".join("---:" for _ in STATUSES) + " |",
    ]
    for dimension in DIMENSIONS:
        lines.append("| " + " | ".join([dimension] + [str(counts[dimension].get(status, 0)) for status in STATUSES]) + " |")
    for field, title in (("category", "Counts by Logical Subsystem"), ("requirement_level", "Counts by Requirement Level"), ("severity", "Counts by Severity if Unsatisfied")):
        lines += [""] + summary_table(obligations, field, title)
    lines += ["", "### Checklist", ""]
    for item in obligations:
        state = completion(item)
        mark = "x" if state == "complete" else " "
        lines.append(f"- [{mark}] `{item['id']}` [{item['requirement_level']}; {item['severity']}] {item['normative_statement']} ({state})")
    lines += ["", "### Obligations", "", "| ID | Category | Requirement | Severity | Normative statement | Lean | MoonBit | Refinement | Tests | Issues |", "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for item in obligations:
        status = item["status"]
        issues = ", ".join(f"[#{issue}](https://github.com/Luna-Flow/QED/issues/{issue})" for issue in item["issues"]) or "-"
        statement = item["normative_statement"].replace("|", "\\|")
        lines.append(f"| `{item['id']}` | {item['category']} | {item['requirement_level']} | {item['severity']} | {statement} | {status['lean']} | {status['moonbit']} | {status['refinement']} | {status['tests']} | {issues} |")
    lines += ["", "### Evidence", ""]
    for item in obligations:
        moonbit = ", ".join(f"`{path}`" for path in item["moonbit_api"]) or "-"
        lean = ", ".join(f"`{entry['path']}::{entry['symbol']}`" for entry in item["lean"]) or "-"
        evidence = ", ".join(f"`{path}`" for path in item["evidence"]) or "-"
        verification = "; ".join(item["verification"]) or "-"
        assumptions = "; ".join(item["assumptions"]) or "-"
        exclusions = "; ".join(item["exclusions"]) or "-"
        lines += [f"#### `{item['id']}`", "", item["normative_statement"], "", f"- Specification: `{item['spec']}::{item['spec_anchor']}`", f"- MoonBit API: {moonbit}", f"- Lean: {lean}", f"- Verification: {verification}", f"- Evidence: {evidence}", f"- Assumptions: {assumptions}", f"- Exclusions: {exclusions}", ""]
    return "\n".join(lines).rstrip() + "\n"


def update_document(generated: str) -> str:
    """Replace the generated section while preserving the authored review text."""
    document = OUTPUT.read_text(encoding="utf-8")
    if document.count(BEGIN_MARKER) != 1 or document.count(END_MARKER) != 1:
        raise ValueError("compliance review must contain exactly one obligation-matrix marker pair")
    if document.index(BEGIN_MARKER) >= document.index(END_MARKER):
        raise ValueError("obligation-matrix markers are out of order")
    before, remainder = document.split(BEGIN_MARKER, 1)
    _, after = remainder.split(END_MARKER, 1)
    return before + BEGIN_MARKER + "\n\n" + generated + "\n" + END_MARKER + after


def main(argv: list[str]) -> int:
    if any(argument != "--write" for argument in argv):
        print("usage: qed_obligations.py [--write]", file=sys.stderr)
        return 2
    try:
        data = read_registry()
        validate(data)
        rendered = render(data)
        updated = update_document(rendered)
        if "--write" in argv:
            OUTPUT.write_text(updated, encoding="utf-8")
        elif OUTPUT.read_text(encoding="utf-8") != updated:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; run python3 tools/qed_obligations.py --write", file=sys.stderr)
            return 1
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"qed obligations: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
