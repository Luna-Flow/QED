# QED Proof-Obligation Matrix

Generated from [`qed_obligations.json`](qed_obligations.json). The dimensions are independent: a Lean proof does not certify the MoonBit implementation, and tests do not establish refinement.

A checked checklist item requires `proved-and-refined` in the refinement dimension. Open means an applicable obligation lacks checked implementation refinement; it does not mean a soundness defect has been demonstrated. Severity records the impact if the obligation is unsatisfied.

Total: **11**; complete: **0**; not applicable: **0**; open: **11**.

## Status Counts

| Dimension | proved and refined | proved abstractly | tested only | implemented unverified | partial | not implemented | known deviation | not applicable |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| lean | 0 | 7 | 0 | 0 | 0 | 1 | 0 | 3 |
| moonbit | 0 | 0 | 3 | 6 | 2 | 0 | 0 | 0 |
| refinement | 0 | 0 | 0 | 0 | 0 | 11 | 0 | 0 |
| tests | 0 | 0 | 10 | 0 | 0 | 0 | 0 | 1 |

## Counts by Logical Subsystem

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| axiom-admission | 1 | 0 | 0 | 1 |
| frontend-boundary | 1 | 0 | 0 | 1 |
| implementation-correspondence | 1 | 0 | 0 | 1 |
| logical-core | 3 | 0 | 0 | 3 |
| theory-extension | 3 | 0 | 0 | 3 |
| trusted-kernel | 2 | 0 | 0 | 2 |

## Counts by Requirement Level

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| required | 11 | 0 | 0 | 11 |

## Counts by Severity if Unsatisfied

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| critical | 7 | 0 | 0 | 7 |
| high | 4 | 0 | 0 | 4 |

## Checklist

- [ ] `HOL-TYPES-001` [required; critical] HOL types, type constructors, non-empty carriers, and type substitution are well-formed. (open)
- [ ] `HOL-TERMS-001` [required; critical] Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning. (open)
- [ ] `HOL-RULES-001` [required; critical] Every primitive theorem rule preserves semantic validity under its stated side conditions. (open)
- [ ] `HOL-EXT-001` [required; critical] Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents. (open)
- [ ] `HOL-EXT-002` [required; high] History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories. (open)
- [ ] `HOL-GROW-001` [required; high] A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation. (open)
- [ ] `HOL-INFINITY-001` [required; high] Infinity admission identifies exactly the canonical object-language infinity sentence. (open)
- [ ] `KERNEL-BOUNDARY-001` [required; critical] Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them. (open)
- [ ] `KERNEL-PROVENANCE-001` [required; critical] A theorem is admissible only in a compatible declaration lineage; sibling histories cannot exchange theorem evidence. (open)
- [ ] `FRONTEND-LOWERING-001` [required; high] Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed. (open)
- [ ] `REFINEMENT-001` [required; critical] MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation. (open)

## Obligations

| ID | Category | Requirement | Severity | Normative statement | Lean | MoonBit | Refinement | Tests | Issues |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `HOL-TYPES-001` | logical-core | required | critical | HOL types, type constructors, non-empty carriers, and type substitution are well-formed. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-TERMS-001` | logical-core | required | critical | Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-RULES-001` | logical-core | required | critical | Every primitive theorem rule preserves semantic validity under its stated side conditions. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-EXT-001` | theory-extension | required | critical | Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#7](https://github.com/Luna-Flow/QED/issues/7), [#8](https://github.com/Luna-Flow/QED/issues/8), [#9](https://github.com/Luna-Flow/QED/issues/9), [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-EXT-002` | theory-extension | required | high | History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories. | proved-abstractly | tested-only | not-implemented | tested-only | [#15](https://github.com/Luna-Flow/QED/issues/15), [#22](https://github.com/Luna-Flow/QED/issues/22) |
| `HOL-GROW-001` | theory-extension | required | high | A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation. | proved-abstractly | partial | not-implemented | not-applicable | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-INFINITY-001` | axiom-admission | required | high | Infinity admission identifies exactly the canonical object-language infinity sentence. | proved-abstractly | partial | not-implemented | tested-only | [#7](https://github.com/Luna-Flow/QED/issues/7) |
| `KERNEL-BOUNDARY-001` | trusted-kernel | required | critical | Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them. | not-applicable | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `KERNEL-PROVENANCE-001` | trusted-kernel | required | critical | A theorem is admissible only in a compatible declaration lineage; sibling histories cannot exchange theorem evidence. | not-applicable | tested-only | not-implemented | tested-only | [#15](https://github.com/Luna-Flow/QED/issues/15), [#22](https://github.com/Luna-Flow/QED/issues/22) |
| `FRONTEND-LOWERING-001` | frontend-boundary | required | high | Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed. | not-applicable | tested-only | not-implemented | tested-only | [#3](https://github.com/Luna-Flow/QED/issues/3), [#4](https://github.com/Luna-Flow/QED/issues/4), [#5](https://github.com/Luna-Flow/QED/issues/5), [#6](https://github.com/Luna-Flow/QED/issues/6) |
| `REFINEMENT-001` | implementation-correspondence | required | critical | MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation. | not-implemented | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |

## Evidence

### `HOL-TYPES-001`

HOL types, type constructors, non-empty carriers, and type substitution are well-formed.

- Specification: `doc/attachments/qed_formal_spec.typ::Type Grammar and Carrier Interpretation`
- MoonBit API: `src/kernel/types.mbt`
- Lean: `formal_verification/QEDFV/HOL/Types.lean::Ty.carrier_nonempty`
- Verification: Lean theorem; MoonBit tests
- Evidence: `formal_verification/QEDFV/HOL/Types.lean`, `src/kernel/kernel_types_test.mbt`
- Assumptions: The fixed total signature and admissible constructor interpretation are explicit Lean parameters.
- Exclusions: No MoonBit-to-Lean refinement theorem exists.

### `HOL-TERMS-001`

Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning.

- Specification: `doc/attachments/qed_formal_spec.typ::Alpha-Equivalence and the Named Boundary`
- MoonBit API: `src/kernel/terms.mbt`
- Lean: `formal_verification/QEDFV/HOL/Terms.lean::Term`, `formal_verification/QEDFV/HOL/Evaluation.lean::Term.eval_substitute`
- Verification: Lean theorem; MoonBit regression tests
- Evidence: `formal_verification/QEDFV/HOL/Evaluation.lean`, `src/kernel/kernel_terms_test.mbt`
- Assumptions: -
- Exclusions: Frontend lowering is outside this proof.

### `HOL-RULES-001`

Every primitive theorem rule preserves semantic validity under its stated side conditions.

- Specification: `doc/attachments/qed_formal_spec.typ::Primitive Inference Rules`
- MoonBit API: `src/kernel/thm.mbt`
- Lean: `formal_verification/QEDFV/HOL/Rules.lean::valid_refl`, `formal_verification/QEDFV/HOL/Derivation.lean::derivation_sound`
- Verification: Lean induction; MoonBit kernel tests
- Evidence: `formal_verification/QEDFV/HOL/Derivation.lean`, `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`
- Assumptions: -
- Exclusions: The Lean derivation constructors are not a source-level refinement of MoonBit constructors.

### `HOL-EXT-001`

Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents.

- Specification: `doc/attachments/qed_formal_spec.typ::Kernel Extension Mapping and Open Gates`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean::extension_derivation_sound`, `formal_verification/QEDFV/HOL/ModelExtension.lean::valid_interpretModels_iff`
- Verification: Lean model-extension proofs; MoonBit gate tests
- Evidence: `formal_verification/QEDFV/HOL/TypeDefGate.lean`, `formal_verification/QEDFV/HOL/ExtensionDerivation.lean`, `src/kernel/kernel_sig_test.mbt`
- Assumptions: Type-definition derivations are interpreted through model pairs.
- Exclusions: Growing-signature syntax and syntactic erasure remain open.

### `HOL-EXT-002`

History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories.

- Specification: `doc/attachments/qed_formal_spec.typ::History-Indexed Extension Derivations`
- MoonBit API: `src/kernel/sig.mbt`, `src/kernel/thm.mbt`
- Lean: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean::typed_extension_derivation_sound`
- Verification: Lean history induction; MoonBit lineage regression tests
- Evidence: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean`, `src/kernel/kernel_audit_test.mbt`
- Assumptions: -
- Exclusions: Lean does not certify the MoonBit lineage representation.

### `HOL-GROW-001`

A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation.

- Specification: `doc/attachments/qed_formal_spec.typ::Signature Integration Boundary`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/DeclarationAllocation.lean::DeclTable.compatible_add`, `formal_verification/QEDFV/HOL/DeclarationAllocationExamples.lean::trueTable2_compatible`
- Verification: Lean finite-allocation lemmas; Concrete Rep/Abs allocation example
- Evidence: `formal_verification/QEDFV/HOL/DeclarationAllocation.lean`, `formal_verification/QEDFV/HOL/DeclarationAllocationExamples.lean`
- Assumptions: The fixed total signature supplies the declared type slot.
- Exclusions: This does not prove constructor allocation, growing-signature model transport, committed-equation preservation, or MoonBit refinement.

### `HOL-INFINITY-001`

Infinity admission identifies exactly the canonical object-language infinity sentence.

- Specification: `doc/attachments/qed_formal_spec.typ::indInfinitySentence`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/Infinity.lean::indInfinitySentence_valid`
- Verification: Lean validity theorem; MoonBit known-deviation marker regressions
- Evidence: `formal_verification/QEDFV/HOL/Infinity.lean`, `src/kernel/kernel_sig_test.mbt`
- Assumptions: -
- Exclusions: The MoonBit gate is not connected to the Lean sentence by a refinement proof.

### `KERNEL-BOUNDARY-001`

Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them.

- Specification: `doc/attachments/qed_formal_spec.typ::The LCF Boundary`
- MoonBit API: `src/kernel/pkg.generated.mbti`, `src/kernel/thm.mbt`, `src/kernel/sig.mbt`
- Lean: -
- Verification: MoonBit package visibility audit; kernel regression tests
- Evidence: `src/kernel/pkg.generated.mbti`, `src/kernel/kernel_audit_test.mbt`, `src/kernel/kernel_immutability_test.mbt`
- Assumptions: MoonBit package abstraction remains enforced by the toolchain.
- Exclusions: No independent proof checker is shipped yet.

### `KERNEL-PROVENANCE-001`

A theorem is admissible only in a compatible declaration lineage; sibling histories cannot exchange theorem evidence.

- Specification: `doc/attachments/qed_formal_spec.typ::Stability Theorem for Scope Mutation`
- MoonBit API: `src/kernel/sig.mbt`, `src/kernel/thm.mbt`
- Lean: -
- Verification: Deterministic adversarial regression corpus
- Evidence: `src/kernel/kernel_audit_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `src/kernel/kernel_immutability_test.mbt`
- Assumptions: -
- Exclusions: Formalization does not model MoonBit state lineage.

### `FRONTEND-LOWERING-001`

Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed.

- Specification: `doc/attachments/qed_formal_spec.typ::Elaboration and Core Typing Judgments`
- MoonBit API: `src/parser/parser.mbt`, `src/elab/resolved.mbt`
- Lean: -
- Verification: Parser/elaborator regression corpus
- Evidence: `src/parser/parser_test.mbt`, `src/elab/elab_test.mbt`
- Assumptions: -
- Exclusions: Frontend tests do not prove kernel soundness or semantic refinement.

### `REFINEMENT-001`

MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation.

- Specification: `doc/attachments/qed_formal_spec.typ::Engineering Correspondence`
- MoonBit API: `src/kernel/types.mbt`, `src/kernel/terms.mbt`, `src/kernel/thm.mbt`, `src/kernel/sig.mbt`
- Lean: -
- Verification: Not yet implemented
- Evidence: `doc/manual/current_workspace_audit.md`, `formal_verification/theory-proof-plan.md`
- Assumptions: -
- Exclusions: Passing MoonBit and Lean builds is not refinement evidence.
