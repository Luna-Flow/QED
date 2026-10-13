# Current workspace audit (2026-10-14)

- Status: point-in-time audit
- Audience: maintainers and reviewers
- Authority: subordinate to [`qed_formal_spec.typ`](../attachments/qed_formal_spec.typ)
- Scope: a short current-state pointer; the dated research report contains the evidence narrative
- Last reviewed: 2026-10-14

This page is intentionally brief. The detailed audit and its reproducible
commands are in the [initial QED verification audit](../../research/qed-verification/2026-10-14-initial-audit.md).
The current implementation mapping is [Specification conformance](conformance.md),
and the current obligation status is generated from
[`qed_obligations.json`](qed_obligations.json).

## Current boundary

- The Typst attachment is the only normative logical specification.
- The Typed HOL development proves the fixed-signature core and history-indexed
  extension closure stated by the formal branch contract.
- The finite `DeclTable` allocation lemmas are checked, but growing-signature
  syntax, embeddings and model transport remain open.
- MoonBit snapshot and theorem-lineage repairs have deterministic regression
  evidence. They are not a MoonBit-to-Lean refinement theorem.
- An independent certificate checker is planned and is not shipped.

## Current risks

The open obligations are tracked by stable IDs in the generated proof-obligation
matrix. Do not infer a stronger result from a passing Lean build, a passing
MoonBit test, or a negative regression case. Each evidence dimension has its own
status and promotion gate.

The former static Typed HOL audit matrix was merged into the generated matrix
and removed to prevent two manually maintained status tables from drifting.
