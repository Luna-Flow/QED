# Typed HOL proof plan

- Status: Typed HOL is the only formal proof line.
- Authority: [QED Typed HOL Core](../doc/attachments/qed_formal_spec.typ).
- Scope: the Lean mathematical calculus and its proved semantic metatheory.
- Excluded: MoonBit refinement, parser/tactic correctness, mutable signature
  provenance, and syntactic derivation erasure for extensions.

## Proof dependency

1. `HOL/Types.lean` defines types, substitutions, denotations, admissibility, and
   proves non-empty carriers.
2. `HOL/Terms.lean` defines intrinsically typed De Bruijn terms, renaming,
   capture-avoiding substitution, and type instantiation.
3. `HOL/Evaluation.lean` defines environments and interpretations and proves
   renaming, substitution, and beta evaluation laws.
4. `HOL/Instantiation.lean` proves choice coherence and semantic type
   instantiation.
5. `HOL/Rules.lean` proves validity preservation for all primitive rules.
6. `HOL/Derivation.lean` proves `derivation_sound` by induction on typed
   derivations.
7. `HOL/Definitions.lean`, `HOL/Specification.lean`, and
   `HOL/TypeDefinitions.lean` prove the semantic extension contracts.
8. `HOL/Conservativity.lean` composes finite semantic extension invariance.
9. `HOL/Concrete.lean` supplies a non-triviality countermodel.
10. `HOL/Soundness.lean` exposes the public package theorem
    `typed_hol_proof_complete`.

## Acceptance matrix

| Obligation | Lean evidence | Status |
| --- | --- | --- |
| Typed syntax and non-empty carriers | `HOL/Types.lean`, `HOL/Terms.lean` | proved |
| Renaming, substitution, beta | `HOL/Evaluation.lean` | proved |
| Type instantiation and choice coherence | `HOL/Instantiation.lean` | proved |
| Primitive rule preservation | `HOL/Rules.lean` | proved |
| Inductive derivation soundness | `HOL/Derivation.lean` | proved |
| Definition semantic equation and old-language invariance | `HOL/Definitions.lean` | proved |
| Specification validity and old-language invariance | `HOL/Specification.lean` | proved |
| Predicate-subtype type-definition laws | `HOL/TypeDefinitions.lean` | proved |
| Finite semantic conservativity | `HOL/Conservativity.lean` | proved |
| Concrete non-triviality | `HOL/Concrete.lean` | proved |
| MoonBit-to-Lean refinement | no Typed HOL theorem | excluded |
| Syntactic derivation erasure | no Typed HOL theorem | excluded |

## Trust basis

The public Typed HOL theorem depends only on Lean/mathlib foundations reported by
`#print axioms`: `propext`, `Classical.choice`, and `Quot.sound`. The project adds
no custom axiom asserting soundness.

## Cleanup and specification acceptance (2026-10-12)

| Item | Observed problem | Change | Acceptance evidence | Status |
| --- | --- | --- | --- | --- |
| Parallel approximation tree | 48 non-HOL Lean modules remained as obsolete evidence | Remove all 48 sources and their project build artifacts | 14 HOL sources plus the root entry; every project import stays within HOL | verified |
| Specification readability and scope | Accumulated manuscript mixed implementation contracts and mathematical claims | Rewrite around typed syntax, ten rules, evaluation, soundness, and scoped extension results | Typst compiles; all eight pages visually inspected; definitions checked against Lean | verified |
| Current audit accuracy | Older audit omitted a reported implementation defect and overstated scope | Preserve implementation mappings and explicitly retain issue #15 | Open issue independently inspected; implementation repair remains deferred | verified within documentation scope |
| Translation consistency | Changed pages left catalogs stale | Regenerate template and translate changed Chinese/Japanese messages | Both catalogs: 2361/2361 translated, zero fuzzy; lunadoc check reports zero errors/warnings | verified |

Verification commands and results:

- `lake build`: success (594 dependency/build jobs); retained theorem signatures
  and proofs are unchanged by this cleanup.
- `#print axioms` for `typed_hol_proof_complete`,
  `typed_canonical_derivation_sound`, `typed_global_semantic_conservativity`,
  and `typed_concrete_consistency`: only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Retained source scan: no `sorry`, `admit`, or custom `axiom`; only HOL and
  Mathlib imports.
- `typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-typed-hol-spec.pdf`:
  success; eight-page output inspected.
- `lunadoc check . --compile`: zero errors and zero warnings.
- `moon info`, `moon fmt`, and `moon check --target all -j 1`: success, with no
  MoonBit source or generated-interface changes.
- `moon test --target <backend> -j 1 --no-parallelize`, run serially for
  `wasm`, `wasm-gc`, `js`, and `native`: 357/357 on each backend. These existing
  tests do not close the known issue #15 coverage gap.

The formal extension results concern pointwise interpretation overrides on a
fixed signature. They do not prove globally fresh declaration allocation,
preservation of earlier gate equations under later overrides, or allocation of
new type constructors. Those limits are explicit in the rewritten specification.
