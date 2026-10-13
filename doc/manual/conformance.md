# Specification conformance

- Status: active implementation evidence
- Audience: maintainers and reviewers
- Authority: [`qed_formal_spec.typ`](../attachments/qed_formal_spec.typ) and current code/tests
- Scope: MoonBit implementation mapping, evidence boundaries and contributor checks
- Last reviewed: 2026-10-14

This page describes what the shipped implementation and its tests establish.
It does not turn implementation evidence into a Lean refinement theorem. The
formal dependency and theorem map lives in
[`formal_verification/theory-proof-plan.md`](../../formal_verification/theory-proof-plan.md);
the branch promotion policy lives in
[`formal_verification/branch_contract.md`](../../formal_verification/branch_contract.md).
The machine-readable registry is [`qed_obligations.json`](qed_obligations.json),
and [`qed_proof_obligations.md`](qed_proof_obligations.md) is generated from it.

## Evidence boundary

1. The Typst attachment is the normative contract.
2. Lean proves the stated Typed HOL calculus and its explicit assumptions.
3. MoonBit source and tests describe the current realization.
4. This page maps implementation surfaces to evidence and records limits.

A passing Lean build does not prove MoonBit behavior. A passing regression does
not prove the absence of all theorem-forging paths. A negative test is evidence
for its reproduced attack, not a universal absence theorem.

## Implementation mapping

| Surface | Implementation | Evidence | Boundary |
| --- | --- | --- | --- |
| Typed core and boundary conversion | `src/kernel/types.mbt`, `src/kernel/terms.mbt` | kernel type and term tests | No Lean source refinement |
| Primitive rules and theorem admission | `src/kernel/thm.mbt` | theorem tests, white-box tests and audit corpus | Opaque `Thm` still depends on immutable transitive data |
| Scoped state and extension gates | `src/kernel/sig.mbt` | signature and audit tests | MoonBit gate correspondence to Lean remains open |
| Snapshot and provenance invariants | `src/kernel/types.mbt`, `terms.mbt`, `thm.mbt`, `sig.mbt` | `kernel_immutability_test.mbt`, sibling-history regressions | Deterministic implementation evidence |
| Elaboration boundary | `src/elab/resolved.mbt` | elaborator tests | Proposition-preservation theorem is open |
| Parser boundary | `src/parser/parser.mbt` | parser tests and raw-offset corpus | Parser correctness is separate from kernel validity |
| Tactic replay | `src/tactics`, `src/prover` | proof-state, positive, negative and unfinished corpora | Replay is not a second proof kernel |
| CLI integration | `src/cmd` | command white-box tests and corpus anchors | CLI output is not logical evidence |

The current kernel repairs snapshot caller-owned arrays where data enters or
leaves kernel-held state: when a theorem is created or lifted back to a term,
when a signature or extension certificate is read, and for constants taken from
the signature. Terms and types a caller builds are the caller's own values and
are not copied by the public constructors and destructors, so building and
walking a deep term stays linear (a regression test builds and walks a chain of
10,000 combinations). Lineage-bearing theorems containing raw shadowable constants are
rejected during rebinding. These repairs address concrete implementation
invariants; they do not promote the `Refinement/MoonBit` branch.

## Claim vocabulary

The registry uses these meanings:

- `proved-and-refined`: a mathematical proof and a checked implementation correspondence exist;
- `proved-abstractly`: the Lean result exists, but source correspondence is absent;
- `tested-only`: executable evidence exists without a formal proof;
- `implemented-unverified`: code exists without sufficient proof or regression evidence;
- `partial`: only a declared subset is covered;
- `not-implemented`: no implementation evidence is claimed;
- `known-deviation`: behavior is deliberately different from the normative contract;
- `not-applicable`: the obligation does not apply to the supported subset.

These dimensions remain independent: Lean, MoonBit, refinement and tests are
reported separately in the generated matrix.

## Documentation example contract

Public examples must be anchored to existing regression tests. The canonical
script corpus is under `src/prover`; tactic examples use `src/tactics`; parser
and CLI examples use their corresponding package tests. A documentation change
that adds or changes a runnable example must update its regression anchor in the
same change. Unsupported behavior must fail or report `unfinished`; it must not
be presented as a successful proof.

## Contributor checks

- `kernel` remains the only theorem-construction boundary.
- `logic` may provide definitions, checked wrappers and replay helpers, but no new authority.
- `elab` freezes resolved identities and fails closed on schema drift.
- `parser` preserves local-over-constant lookup and raw source offsets.
- `tactics` returns a theorem only after replay through checked kernel paths.
- `prover` reports `Ok` only when replay succeeds and keeps unfinished proofs explicit.
- `cmd` remains a thin integration layer.
- Extension certificates are audit artifacts, not substitutes for theorem acceptance.

## Reproduction

The narrow implementation gate is:

```text
moon info
moon fmt
moon check --target all --deny-warn
moon test --target native --deny-warn
moon test --target wasm --deny-warn
moon test --target wasm-gc --deny-warn
moon test --target js --deny-warn
python3 tools/qed_obligations.py
```

The broader formal and documentation gates are listed in the dated
[initial verification audit](../../research/qed-verification/2026-10-14-initial-audit.md).
Do not lower strictness, discard failed cases or change denominators to make a
conformance result pass.
