# QED formal specification audit matrices

Audit basis: `doc/attachments/qed_formal_spec.typ`, `formal_verification/QEDFV`, and `src/kernel` at the worktree base `ba385bc`. “Lean proved” below means the **stated Lean proposition** typechecks; it does not automatically certify the stronger mathematical sentence in the manuscript.

Status vocabulary is fixed: `proved` means the stated proposition is independently established; `conditional` means it is established only under explicit law/simulation premises; `implementation-open` means the remaining work is the excluded MoonBit/refinement layer; `open` means an in-scope proof is missing; `bug` means a concrete defect has a reproducer. GitHub references use the repository issues cited below.

## 2026-10-12 typed HOL core follow-up

`formal_verification/QEDFV/HOL` now contains the formal soundness mainline: an
independently typed HOL core with constructed carriers, non-emptiness, typed
renaming/substitution/beta laws, general open-context `ABS`, exact assumption
discharge `DEDUCT`, typed term instantiation, and typed polymorphic `INST_TYPE`.
`Derivation.lean` closes the corresponding inductive `derivation_sound` theorem;
`Instantiation.lean` constructs natural choice coherence. `Concrete.lean` supplies
a closed non-triviality countermodel; `TypeDefinitions.lean`, `Definitions.lean`,
and `Specification.lean` supply typed semantic contracts for the extension gates.
`Transport.lean` proves validity transport and bidirectional old-language
invariance; `Conservativity.lean` proves finite extension composition; and
`Soundness.lean` exposes the canonical model and theorem entry points. These
results close the Typed HOL proof. Distinct-state syntactic erasure and other
legacy boundary work are implementation-open only.

## Issue matrix

| ID | Class | Observed evidence and cause | Required contract / decision | Verification and acceptance | Status | Issues |
| --- | --- | --- | --- | --- | --- | --- |
| I1 | Semantic deviation | The legacy `DerivationObject`/`Erasure*` package proves only same-state tree rewriting. | The Typed HOL semantic theorem is `HOL/Conservativity.lean:typed_global_semantic_conservativity`; distinct-state syntactic erasure is implementation-open. | `lake build`; axiom scan of the Typed HOL theorem. | implementation-open | #16 |
| I2 | Semantic deviation | The legacy `TypeDefOK` executable gate remains weaker than the mathematical contract. | The Typed HOL mainline now states the required predicate family, proves non-empty carriers for every admissible valuation, and proves semantic Abs/Rep equations. The legacy gate still needs a correspondence proof. | `HOL/TypeDefinitions.lean`; legacy gate correspondence remains separate. | proved | #16 |
| I3 | Semantic deviation | The legacy `DefOK` executable gate and theorem-shape helper do not establish the full semantic equation contract. | The Typed HOL mainline supplies a fresh-constant interpretation, proves the definition equation, and proves bidirectional validity invariance for sequents excluding the fresh id. The implementation gate still needs a checked derivation and recursive occurrence correspondence. | `HOL/Definitions.lean:valid_definition_equation`, `valid_definition_old_language_iff`; source-level gate correspondence remains open. | proved | #16 |
| I4 | Semantic deviation | The legacy `SpecOK` executable gate and trusted constructor do not by themselves establish the derived semantic theorem. | The Typed HOL mainline supplies a typed fresh-constant interpretation, proves the Choice-derived property, and proves bidirectional old-language validity invariance. The implementation path still needs a checked Choice + definition derivation. | `HOL/Specification.lean:SpecificationGate.valid_constant`, `valid_old_language_iff`; source comparison and refinement remain open. | proved | #16 |
| I5 | Proof/oracle gap | Concrete named/De Bruijn conversion remains an implementation bridge. | Typed HOL proves all intrinsic syntax, substitution, beta, and evaluation laws independently. | `HOL/Evaluation.lean`; MoonBit boundary remains excluded. | implementation-open | #16 |
| I6 | Proof/oracle gap | The legacy `Semantics/Model.lean` is a transitional law bundle. | Typed HOL constructs `canonicalConstVal`, `canonicalModel`, and rule semantics without model law fields. | `HOL/Soundness.lean`; axiom scan. | proved | #16 |
| I7 | Integration issue | Reserved-symbol identity and named theorem representation belong to the MoonBit boundary. | Typed HOL represents equality and choice intrinsically and cannot shadow them. | `HOL/Terms.lean`; implementation audit remains separate. | implementation-open | #16 |
| I8 | Proof/oracle gap | The legacy `Kernel/RuleSoundness.lean` is a transitional representation package. | The exact typed discharge theorem is `HOL/Rules.lean:valid_deduct`, and typed derivation induction uses it directly. | `lake build QEDFV.HOL.Rules`. | proved | #16 |
| I9 | Documentation gap | The old changelog's `[PASS]` and `Open items: None` predate this audit and claim full closure from compilation. | Preserve history but append a dated correction and current proof-status ledger. | Typst build and audit matrix reconciliation. | proved | #16 |
| I10 | Circularity | The old envelope/model package encoded transitional implementation assumptions. | Typed HOL separates structural carriers, rule preservation, and extension semantics; no soundness conclusion is stored in a model. | Lean build; `HOL/Derivation.lean` and `HOL/Conservativity.lean`. | proved | #14 |
| I11 | Circularity | The legacy `AdmissibleModelClass` law bundle was an assumption-based approximation. | Typed HOL proves `derivation_sound` by induction and constructs the canonical model independently. | Lean build; no Typed HOL soundness field exists. | proved | #16 |
| I12 | Circularity | `FaithfulRealization` previously assumed `accepts -> Derivable` through `ruleFidelity`, then used that assumption as implementation transfer. | Require recursive `CheckedDerivation` evidence and reconstruct `Derivable` with `checked_derivation_reconstructs_derivable`; legacy replay helpers are no longer release evidence. | Lean build; transfer uses `CheckedDerivation`. | proved | #16 |
| I13 | Semantic naming | The old release theorem called same-state gate-tag erasure “global conservativity”. | Typed HOL now uses a finite interpretation sequence with explicit old-language premises; the legacy theorem remains implementation-open. | `HOL/Conservativity.lean:valid_interpretSequence_iff`. | proved | #16 |
| I14 | Bug | The forked-state counterexample shows sibling `KernelState` values can allocate the same `ConstId`; `Thm` carries no state lineage and admissibility checks the name/id shape without checking the source definition body, allowing `|- c = T` from one fork to combine with `c := F` from another. | Treat theorem provenance as a kernel invariant: reject theorem values from sibling histories, or use globally unique identities. Add a regression reproducer before claiming implementation soundness. | Issue #15 reproducer; current Lean abstract pack does not model MoonBit state lineage. | bug | #15 |

## Proof-obligation matrix

| Obligation | Mathematical target | Current evidence | Next witness | Status | Issues |
| --- | --- | --- | --- | --- | --- |
| P1 HOL/STT syntax and typing | Every resolved term is well-typed over an admissible signature with nonempty type carriers. | Intrinsic `HOL.Term` and `Ty.carrier_nonempty`. | MoonBit `DbTerm` correspondence is excluded. | proved | #16 |
| P2 Scope/history | Pop changes only `S`; admitted heads persist in `T`; resolved identities remain stable. | Typed HOL terms carry resolved typed identities without a mutable scope layer. | Concrete scope/provenance correspondence is excluded. | implementation-open | #15,#16 |
| P3 Definition admission | Fresh, closed, typed, acyclic `c = r`, with `TVars(r) ⊆ TVars(τ)`; equation theorem is derivable. | Typed HOL `DefinitionGate` intrinsically supplies closure/typing and explicitly stores `typeVarsClosed`; it proves the fresh equation and old-language validity iff. | Legacy syntax-gate correspondence is excluded. | proved | #16 |
| P4 Type definition | Witnessed nonempty predicate family and Abs/Rep equations under all parameter interpretations. | `HOL/TypeDefinitions.lean` proves non-emptiness, `abs_rep`, range, and `rep_abs_of_pred` for every admissible valuation. | Legacy `TypeDefOK` correspondence is excluded. | proved | #16 |
| P5 Specification | Certified witness plus Choice derives `P(c)` through `DefOK`. | `HOL/Specification.lean` proves validity for an interpreted fresh constant and `SpecificationExtension.valid_gate` derives it from a typed `Derivation`; finite old-language invariance is proved. | Legacy admission-path correspondence is excluded. | proved | #16 |
| P6 Boundary/substitution/beta | Typed syntax, substitution, beta, and denotation commute. | `HOL/Evaluation.lean` proves typed renaming, substitution, beta, and `HOL/Instantiation.lean` proves type-instantiation coherence. | Named/De Bruijn correspondence is implementation-open. | proved | #16 |
| P7 Primitive soundness | Typed HOL derivations preserve validity in the canonical model. | `HOL/Rules.lean`, `HOL/Derivation.lean`, and `HOL/Instantiation.lean:select_natural`. | MoonBit correspondence is excluded. | proved | #16 |
| P8 Conservativity | Old-language validity is invariant under each typed extension and finite sequences. | `HOL/Definitions.lean`, `HOL/Specification.lean`, and `HOL/Conservativity.lean`. | Distinct-state syntactic simulation is implementation-open. | proved | #16 |
| P9 Implementation transfer | Every exported MoonBit theorem path reconstructs a Part I derivation. | This is explicitly the excluded MoonBit refinement. | Bind MoonBit paths to `CheckedDerivation` later. | implementation-open | #16 |

Current verification in the independent worktree: `lake build` passed (642 jobs);
`typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-formal-audit.pdf`,
`moon check`, `moon test` (357/357), and `lunadoc check . --compile` passed.
These checks establish the Typed HOL semantic proof and the current implementation
regression suite. They do not claim the excluded MoonBit-to-Lean refinement,
distinct-state provenance repair, or concrete boundary correspondence.
