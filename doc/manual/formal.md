# Formal description

- Status: active
- Audience: kernel maintainers, formalization contributors, reviewers
- Authority: the formal specification is normative; this page is descriptive
- Scope: specification entry point, verification boundary, and revision summary
- Last reviewed: 2026-10-15

QED has one normative mathematical specification. The Typst source defines the
typed HOL calculus, kernel rules, extension gates, history discipline, frontend
boundary, and engineering correspondence target. The Lean development in
`formal_verification/QEDFV/HOL` proves selected mathematical branches of that
calculus. MoonBit tests establish implementation behavior; they do not by
themselves establish a MoonBit-to-Lean refinement.

The published specification is generated from the checked-in attachment below.
The documentation site compiles the Typst source and renders the PDF in an
embedded reader; GitHub users can still open the source directly.

[QED formal specification](../attachments/qed_formal_spec.typ)

## Verification boundary

The current evidence order is:

1. The Typst specification defines the normative mathematical contract.
2. The Typed HOL development proves the fixed-signature core and supported
   history-indexed extension results.
3. MoonBit code and regression tests establish the shipped implementation
   boundary and fail-closed behavior.
4. The compliance review records the obligation-by-obligation status across
   Lean, MoonBit, refinement, and tests.

The formal branch contract and proof plan remain working documents for the
formalization line. They describe promotion gates and mathematical limits;
they do not add specification authority.

## Current revision

The current revision includes the history-indexed extension calculus, explicit
`DefOK`, `TypeDefOK`, and `SpecOK` gates, typed De Bruijn core rules, constant
schema instantiation, theorem lineage checks, and the frontend identity
boundary. The latest layout revision also separates annotated blocks by role
and keeps long equations within the page width.

Historical specification revisions are recorded in version control. Current
status and residual evidence are maintained in the [compliance review](conformance.md)
and its generated proof-obligation section.
