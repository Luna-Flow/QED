# Compliance review

- Status: active implementation evidence
- Audience: maintainers and reviewers
- Authority: [`qed_formal_spec.typ`](../attachments/qed_formal_spec.typ) and current code/tests
- Scope: implementation mapping, proof obligations, evidence boundaries, governance and contributor checks
- Last reviewed: 2026-10-15

This page is QED's single compliance review table. It describes what the shipped implementation and its tests establish.
It does not turn implementation evidence into a Lean refinement theorem. The
formal dependency and theorem map lives in
[`formal_verification/theory-proof-plan.md`](../../formal_verification/theory-proof-plan.md);
the branch promotion policy lives in
[`formal_verification/branch_contract.md`](../../formal_verification/branch_contract.md).
The machine-readable registry is [`qed_obligations.json`](qed_obligations.json),
and the proof-obligation matrix is generated into this page below.

## Document architecture

The repository keeps three focused review surfaces:

- [Syntax guide](syntax.md): the shipped theorem-script input grammar.
- [Formal description](formal.md): the normative specification entry point and
  its embedded PDF preview.
- This page: implementation conformance, proof obligations, evidence limits,
  and contributor checks.

Package API, design, tutorial, and user-manual pages explain the shipped
surface. They do not create parallel governance, audit, changelog, or proof
matrix authorities.

## Package and documentation governance

The dependency direction is `kernel -> logic/elab -> parser -> tactics -> prover -> cmd`.
Only `kernel` may construct theorem objects. Upper layers may organize checked
helpers, parse and elaborate input, transform proof states, replay checked
paths, and report diagnostics; they may not add logical authority.

Each package keeps its production and test alias entry points explicit. Changes
to semantic boundaries, gates, scope, replay, parser lowering, or theorem
lineage must update implementation, regression tests, and this review table.
Documentation uses one canonical page per concern and keeps research notes
under `research/`; research notes are evidence records, not shipped contracts.

`alias.mbt` exposes only stable imports needed by production code.
`alias_test.mbt` mirrors those imports before adding test-only imports, and
explicitly imports its own package symbols with `using @<package> {...}`.
Alias headers state their scope and maintenance rules; aliases are not a second
public API or an unbounded re-export table. The dependency-free `kernel` has
only `alias_test.mbt`.

`research_rewrite` depends only on `kernel` and `logic`, and no shipped package
depends on it. `cmd` is executable and cannot be imported. Reverse dependencies
require a design review; prefer a neutral data structure or explicit bridge.
Parser lowering, tactic execution, orchestration, diagnostic rendering, and
corpus data keep separate responsibilities.

Update code and tests first, then the user manual, affected package pages,
this review, repository summaries, and relevant research records. Check that
generated `.mbti` changes match the intended public boundary. Maintenance-facing
pages declare status, audience, authority, scope, and review date; new research
belongs under `research/<topic>/` and declares its unshipped, non-authoritative
status.

## Current evidence boundary

The current Typed HOL results cover the fixed-signature core, history-indexed
extension closure, and finite declaration-allocation facts. MoonBit snapshot,
scope, and theorem-lineage repairs have deterministic regression evidence.
Growing-signature transport, source-level MoonBit refinement, syntactic
type-definition erasure, and an independent certificate checker remain open
obligations. A passing Lean build or MoonBit test must not be reported as a
refinement proof.

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

<!-- BEGIN GENERATED OBLIGATION MATRIX -->

## Proof-obligation matrix

Generated from [`qed_obligations.json`](qed_obligations.json). The dimensions are independent: a Lean proof does not certify the MoonBit implementation, and tests do not establish refinement.

A checked checklist item requires `proved-and-refined` in the refinement dimension. Open means an applicable obligation lacks checked implementation refinement; it does not mean a soundness defect has been demonstrated. Severity records the impact if the obligation is unsatisfied.

Total: **12**; complete: **0**; not applicable: **0**; open: **12**.

### Status Counts

| Dimension | proved and refined | proved abstractly | tested only | implemented unverified | partial | not implemented | known deviation | not applicable |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| lean | 0 | 7 | 0 | 0 | 1 | 1 | 0 | 3 |
| moonbit | 0 | 0 | 4 | 6 | 1 | 1 | 0 | 0 |
| refinement | 0 | 0 | 0 | 0 | 0 | 12 | 0 | 0 |
| tests | 0 | 0 | 10 | 0 | 0 | 1 | 0 | 1 |

### Counts by Logical Subsystem

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| axiom-admission | 1 | 0 | 0 | 1 |
| frontend-boundary | 1 | 0 | 0 | 1 |
| implementation-correspondence | 1 | 0 | 0 | 1 |
| logical-core | 3 | 0 | 0 | 3 |
| theory-extension | 4 | 0 | 0 | 4 |
| trusted-kernel | 2 | 0 | 0 | 2 |

### Counts by Requirement Level

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| required | 12 | 0 | 0 | 12 |

### Counts by Severity if Unsatisfied

| Group | Total | Complete | Not applicable | Open |
| --- | ---: | ---: | ---: | ---: |
| critical | 7 | 0 | 0 | 7 |
| high | 5 | 0 | 0 | 5 |

### Checklist

- [ ] `HOL-TYPES-001` [required; critical] HOL types, type constructors, non-empty carriers, and type substitution are well-formed. (open)
- [ ] `HOL-TERMS-001` [required; critical] Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning. (open)
- [ ] `HOL-RULES-001` [required; critical] Every primitive theorem rule preserves semantic validity under its stated side conditions. (open)
- [ ] `HOL-EXT-001` [required; critical] Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents. (open)
- [ ] `HOL-EXT-002` [required; high] History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories. (open)
- [ ] `HOL-ERASE-001` [required; high] A derivation at a history that begins with a definition, a specification or a type definition yields a derivation at the preceding history in which every occurrence of the declared constant is replaced by its instantiated definition, by the choice term of its instantiated predicate, or (for a type definition) in which the defined type is translated to its representation type; sequents not mentioning the declared symbols are derivable unchanged. (open)
- [ ] `HOL-GROW-001` [required; high] A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation. (open)
- [ ] `HOL-INFINITY-001` [required; high] The executable infinity registration is an audit marker; the canonical object-language infinity sentence is established by the Lean rule, not by the MoonBit gate. (open)
- [ ] `KERNEL-BOUNDARY-001` [required; critical] Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them. (open)
- [ ] `KERNEL-PROVENANCE-001` [required; critical] A theorem is admissible only in a compatible declaration lineage; divergent sibling histories cannot exchange theorem evidence. (open)
- [ ] `FRONTEND-LOWERING-001` [required; high] Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed. (open)
- [ ] `REFINEMENT-001` [required; critical] MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation. (open)

### Obligations

| ID | Category | Requirement | Severity | Normative statement | Lean | MoonBit | Refinement | Tests | Issues |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `HOL-TYPES-001` | logical-core | required | critical | HOL types, type constructors, non-empty carriers, and type substitution are well-formed. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-TERMS-001` | logical-core | required | critical | Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-RULES-001` | logical-core | required | critical | Every primitive theorem rule preserves semantic validity under its stated side conditions. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-EXT-001` | theory-extension | required | critical | Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents. | proved-abstractly | implemented-unverified | not-implemented | tested-only | [#7](https://github.com/Luna-Flow/QED/issues/7), [#8](https://github.com/Luna-Flow/QED/issues/8), [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-EXT-002` | theory-extension | required | high | History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories. | proved-abstractly | tested-only | not-implemented | tested-only | [#15](https://github.com/Luna-Flow/QED/issues/15), [#22](https://github.com/Luna-Flow/QED/issues/22) |
| `HOL-ERASE-001` | theory-extension | required | high | A derivation at a history that begins with a definition, a specification or a type definition yields a derivation at the preceding history in which every occurrence of the declared constant is replaced by its instantiated definition, by the choice term of its instantiated predicate, or (for a type definition) in which the defined type is translated to its representation type; sequents not mentioning the declared symbols are derivable unchanged. | partial | not-implemented | not-implemented | not-implemented | [#17](https://github.com/Luna-Flow/QED/issues/17), [#50](https://github.com/Luna-Flow/QED/issues/50) |
| `HOL-GROW-001` | theory-extension | required | high | A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation. | proved-abstractly | partial | not-implemented | not-applicable | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `HOL-INFINITY-001` | axiom-admission | required | high | The executable infinity registration is an audit marker; the canonical object-language infinity sentence is established by the Lean rule, not by the MoonBit gate. | proved-abstractly | tested-only | not-implemented | tested-only | [#7](https://github.com/Luna-Flow/QED/issues/7) |
| `KERNEL-BOUNDARY-001` | trusted-kernel | required | critical | Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them. | not-applicable | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |
| `KERNEL-PROVENANCE-001` | trusted-kernel | required | critical | A theorem is admissible only in a compatible declaration lineage; divergent sibling histories cannot exchange theorem evidence. | not-applicable | tested-only | not-implemented | tested-only | [#15](https://github.com/Luna-Flow/QED/issues/15), [#22](https://github.com/Luna-Flow/QED/issues/22) |
| `FRONTEND-LOWERING-001` | frontend-boundary | required | high | Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed. | not-applicable | tested-only | not-implemented | tested-only | [#3](https://github.com/Luna-Flow/QED/issues/3), [#4](https://github.com/Luna-Flow/QED/issues/4), [#5](https://github.com/Luna-Flow/QED/issues/5), [#6](https://github.com/Luna-Flow/QED/issues/6) |
| `REFINEMENT-001` | implementation-correspondence | required | critical | MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation. | not-implemented | implemented-unverified | not-implemented | tested-only | [#17](https://github.com/Luna-Flow/QED/issues/17) |

### Evidence

#### `HOL-TYPES-001`

HOL types, type constructors, non-empty carriers, and type substitution are well-formed.

- Specification: `doc/attachments/qed_formal_spec.typ::Type Grammar and Carrier Interpretation`
- MoonBit API: `src/kernel/types.mbt`
- Lean: `formal_verification/QEDFV/HOL/Types.lean::Ty.carrier_nonempty`
- Verification: Lean theorem; MoonBit tests
- Evidence: `formal_verification/QEDFV/HOL/Types.lean`, `src/kernel/kernel_types_test.mbt`
- Assumptions: The fixed total signature and admissible constructor interpretation are explicit Lean parameters.
- Exclusions: No MoonBit-to-Lean refinement theorem exists.

#### `HOL-TERMS-001`

Typed terms, alpha-equivalence, capture-avoiding substitution, beta evaluation, and type instantiation preserve typing and meaning.

- Specification: `doc/attachments/qed_formal_spec.typ::Alpha-Equivalence and the Named Boundary`
- MoonBit API: `src/kernel/terms.mbt`
- Lean: `formal_verification/QEDFV/HOL/Terms.lean::Term`, `formal_verification/QEDFV/HOL/Evaluation.lean::Term.eval_substitute`
- Verification: Lean theorem; MoonBit regression tests
- Evidence: `formal_verification/QEDFV/HOL/Evaluation.lean`, `src/kernel/kernel_terms_test.mbt`
- Assumptions: -
- Exclusions: Frontend lowering is outside this proof.

#### `HOL-RULES-001`

Every primitive theorem rule preserves semantic validity under its stated side conditions.

- Specification: `doc/attachments/qed_formal_spec.typ::Primitive Inference Rules`
- MoonBit API: `src/kernel/thm.mbt`
- Lean: `formal_verification/QEDFV/HOL/Rules.lean::valid_refl`, `formal_verification/QEDFV/HOL/Derivation.lean::derivation_sound`, `formal_verification/QEDFV/HOL/ConnectiveRules.lean::valid_classical`
- Verification: Lean induction; MoonBit kernel tests
- Evidence: `formal_verification/QEDFV/HOL/Derivation.lean`, `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `formal_verification/QEDFV/HOL/ConnectiveRules.lean`
- Assumptions: -
- Exclusions: The Lean derivation constructors are not a source-level refinement of MoonBit constructors.

#### `HOL-EXT-001`

Definition, specification, and type-definition extensions have their stated local semantic laws and preserve validity of old-language sequents.

- Specification: `doc/attachments/qed_formal_spec.typ::Kernel Extension Mapping and Open Gates`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean::extension_derivation_sound`, `formal_verification/QEDFV/HOL/ModelExtension.lean::valid_interpretModels_iff`
- Verification: Lean model-extension proofs; MoonBit gate tests
- Evidence: `formal_verification/QEDFV/HOL/TypeDefGate.lean`, `formal_verification/QEDFV/HOL/ExtensionDerivation.lean`, `src/kernel/kernel_sig_test.mbt`
- Assumptions: Type-definition derivations are interpreted through model pairs.
- Exclusions: Growing-signature syntax and syntactic erasure remain open.

#### `HOL-EXT-002`

History-indexed derivations require extension witnesses at the preceding history and preserve old-language validity across supported histories.

- Specification: `doc/attachments/qed_formal_spec.typ::History-Indexed Extension Derivations`
- MoonBit API: `src/kernel/sig.mbt`, `src/kernel/thm.mbt`
- Lean: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean::typed_extension_derivation_sound`
- Verification: Lean history induction; MoonBit lineage regression tests
- Evidence: `formal_verification/QEDFV/HOL/ExtensionDerivation.lean`, `src/kernel/kernel_audit_test.mbt`
- Assumptions: -
- Exclusions: Lean does not certify the MoonBit lineage representation.

#### `HOL-ERASE-001`

A derivation at a history that begins with a definition, a specification or a type definition yields a derivation at the preceding history in which every occurrence of the declared constant is replaced by its instantiated definition, by the choice term of its instantiated predicate, or (for a type definition) in which the defined type is translated to its representation type; sequents not mentioning the declared symbols are derivable unchanged.

- Specification: `doc/attachments/qed_formal_spec.typ::History-Indexed Extension Derivations`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/Unfold.lean::HistoryDerivation.erase_definition`, `formal_verification/QEDFV/HOL/Unfold.lean::HistoryDerivation.definition_conservative`, `formal_verification/QEDFV/HOL/SpecErasure.lean::HistoryDerivation.erase_specification`, `formal_verification/QEDFV/HOL/SpecErasure.lean::HistoryDerivation.specification_conservative`, `formal_verification/QEDFV/HOL/TdMain.lean::typedef_conservative`, `formal_verification/QEDFV/HOL/UnfoldBelow.lean::HistoryDerivation.erase_below`, `formal_verification/QEDFV/HOL/TdBelow.lean::TypeDefGate.typedef_conservative_unfold`, `formal_verification/QEDFV/HOL/TdBelow.lean::TypeDefGate.typedef_conservative_old`
- Verification: Lean induction on history derivations; Lean annotation-erasure laws for type instantiation
- Evidence: `formal_verification/QEDFV/HOL/Unfold.lean`, `formal_verification/QEDFV/HOL/TermLaws.lean`, `formal_verification/QEDFV/HOL/SpecErasure.lean`, `formal_verification/QEDFV/HOL/TdMain.lean`, `research/qed-verification/2026-10-18-typedef-erasure.md`, `formal_verification/QEDFV/HOL/UnfoldBelow.lean`, `formal_verification/QEDFV/HOL/TdBelow.lean`
- Assumptions: -
- Exclusions: Type-definition erasure is proved for a type definition without type parameters above any list of definitions and specifications (which may be polymorphic).; Type definitions with parameters and type definitions above older type definitions are not proved.; Lean does not certify the MoonBit kernel.

#### `HOL-GROW-001`

A finite declaration table records fresh constant allocation and preserves compatibility with the fixed total signature; old declarations remain available after a fresh allocation.

- Specification: `doc/attachments/qed_formal_spec.typ::Signature Integration Boundary`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/DeclarationAllocation.lean::DeclTable.compatible_add`, `formal_verification/QEDFV/HOL/DeclarationAllocationExamples.lean::trueTable2_compatible`
- Verification: Lean finite-allocation lemmas; Concrete Rep/Abs allocation example
- Evidence: `formal_verification/QEDFV/HOL/DeclarationAllocation.lean`, `formal_verification/QEDFV/HOL/DeclarationAllocationExamples.lean`
- Assumptions: The fixed total signature supplies the declared type slot.
- Exclusions: This does not prove constructor allocation, growing-signature model transport, committed-equation preservation, or MoonBit refinement.

#### `HOL-INFINITY-001`

The executable infinity registration is an audit marker; the canonical object-language infinity sentence is established by the Lean rule, not by the MoonBit gate.

- Specification: `doc/attachments/qed_formal_spec.typ::indInfinitySentence`
- MoonBit API: `src/kernel/sig.mbt`
- Lean: `formal_verification/QEDFV/HOL/Infinity.lean::indInfinitySentence_valid`
- Verification: Lean validity theorem; MoonBit marker regressions
- Evidence: `formal_verification/QEDFV/HOL/Infinity.lean`, `src/kernel/kernel_sig_test.mbt`
- Assumptions: -
- Exclusions: The MoonBit marker does not check that the registered theorem states that ind is infinite, and is not connected to the Lean sentence by a refinement proof.

#### `KERNEL-BOUNDARY-001`

Only checked kernel constructors and extension gates can produce theorem objects; frontend code cannot forge them.

- Specification: `doc/attachments/qed_formal_spec.typ::The LCF Boundary`
- MoonBit API: `src/kernel/pkg.generated.mbti`, `src/kernel/thm.mbt`, `src/kernel/sig.mbt`
- Lean: -
- Verification: MoonBit package visibility audit; kernel regression tests
- Evidence: `src/kernel/pkg.generated.mbti`, `src/kernel/kernel_audit_test.mbt`, `src/kernel/kernel_immutability_test.mbt`
- Assumptions: MoonBit package abstraction remains enforced by the toolchain.
- Exclusions: No independent proof checker is shipped yet.

#### `KERNEL-PROVENANCE-001`

A theorem is admissible only in a compatible declaration lineage; divergent sibling histories cannot exchange theorem evidence.

- Specification: `doc/attachments/qed_formal_spec.typ::Stability Theorem for Scope Mutation`
- MoonBit API: `src/kernel/sig.mbt`, `src/kernel/thm.mbt`
- Lean: -
- Verification: Deterministic adversarial regression corpus
- Evidence: `src/kernel/kernel_audit_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `src/kernel/kernel_immutability_test.mbt`
- Assumptions: -
- Exclusions: Formalization does not model MoonBit state lineage.

#### `FRONTEND-LOWERING-001`

Parsing and elaboration preserve the proposition and resolved constant identity supplied to the kernel, or fail closed.

- Specification: `doc/attachments/qed_formal_spec.typ::Elaboration and Core Typing Judgments`
- MoonBit API: `src/parser/parser.mbt`, `src/elab/resolved.mbt`
- Lean: -
- Verification: Parser/elaborator regression corpus
- Evidence: `src/parser/parser_test.mbt`, `src/elab/elab_test.mbt`
- Assumptions: -
- Exclusions: Frontend tests do not prove kernel soundness or semantic refinement.

#### `REFINEMENT-001`

MoonBit types, terms, theorem objects, state transitions, and theorem constructors are connected to the Typed HOL calculus by a checked refinement or proof-producing translation.

- Specification: `doc/attachments/qed_formal_spec.typ::Engineering Correspondence`
- MoonBit API: `src/kernel/types.mbt`, `src/kernel/terms.mbt`, `src/kernel/thm.mbt`, `src/kernel/sig.mbt`
- Lean: -
- Verification: Not yet implemented
- Evidence: `research/qed-verification/2026-10-14-initial-audit.md`, `formal_verification/theory-proof-plan.md`
- Assumptions: -
- Exclusions: Passing MoonBit and Lean builds is not refinement evidence.

<!-- END GENERATED OBLIGATION MATRIX -->

The broader formal and documentation gates are listed in the dated
[initial verification audit](../../research/qed-verification/2026-10-14-initial-audit.md).
Do not lower strictness, discard failed cases or change denominators to make a
conformance result pass.
