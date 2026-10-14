# Formal specification changelog

- Status: archival reference
- Audience: specification maintainers and reviewers
- Authority: the current Typst specification remains normative; this file records revisions only
- Scope: historical changes to the formal specification and its Lean evidence
- Last reviewed: 2026-10-14

This is a history file, not a current proof-status entry point. Use the
[branch contract](../../formal_verification/branch_contract.md), the
[Typed HOL proof plan](../../formal_verification/theory-proof-plan.md) and the
[generated obligation matrix](qed_proof_obligations.md) for current status.

## 2026-10-14 Typography and structure

- Document style: one visual system for annotated blocks (a coloured left bar, as in the Lean 4 annotations), numbered definitions, propositions, lemmas, theorems and corollaries, proofs closed with a mark, table of contents, running header and footer, booktabs-style tables, and unnumbered appendices.
- Display formulas written as an empty `$$` pair (which rendered the formula source as text) are now real display equations; the three history-derivation rules are typeset as inference rules.
- No mathematical content changed.

## 2026-10-15 Theorem lineage follow-up (#22)

- Documented declaration-lineage admission in the kernel API and design pages,
  including the distinction between divergent sibling histories and branches
  that perform the same lineage events.
- Added regression coverage for identical sibling histories, a theorem carried
  through a pushed and popped scope, and `thm_bind_const_ids` rejection across
  divergent sibling histories. The implementation repair from [#21](https://github.com/Luna-Flow/QED/issues/21)
  therefore has its requested MoonBit follow-up coverage; the MoonBit-to-Lean
  refinement remains a separate obligation tracked by [#17](https://github.com/Luna-Flow/QED/issues/17).
- Measured the lineage cost with the reproducible native-release benchmark in
  `src/bench`: build medians for 0, 100, 300 and 500 definitions were about
  0.58, 544, 2674 and 6525 microseconds, while checked `inst` medians were
  about 1.73, 3.63, 6.90 and 12.32 microseconds (ten samples per case). The
  current representation is acceptable at this scale; no interning or hash
  chain is introduced without a workload that justifies it.
- Completed the `zh_CN` and `ja_JP` translations for the lineage documentation.

## 2026-10-13 Type definitions as history-indexed derivations

- `ExtensionDerivation` is indexed by histories of `ModelExtension` steps and has a
  `typedef` constructor: one constructor with the selector `TypeDefLaw` (`Abs (Rep a) = a`,
  `P (Rep a)`, `P r ⊢ Rep (Abs r) = r`), a mandatory hypothesis-free witness derivation
  `⊢ P w` at the preceding history, and carried freshness of `k`, `rep`, `abs`. `weaken`
  across a type definition requires the sequent not to mention `k`, `rep` or `abs`.
- `extension_derivation_sound` now returns validity at the history's model pair
  `(κ, I)` (`interpretModels`) for a local base model; the typed wrappers use the canonical
  models. This changes the statement of the earlier theorem (histories of `Extension κ S`
  over a fixed `κ` are replaced by histories of `ModelExtension`).
- The definition and specification closure fields are now stated for `Term.annotVars`
  (the kernel's `term_tyvars` counts binder domains); `type_vars_closed` and
  `instType_type_vars_closed` are kept for `Term.typeVars` as consequences.
- Proved that every declaration step preserves locality, hence
  `valid_interpretModels_iff`, `typed_global_semantic_conservativity_models` and
  `extension_derivation_old_language_valid` for histories with type definitions.
- Worked example: the one-element subtype of `bool` with its witness derivation, the three
  laws as derivations, an old-language theorem lifted with `weaken`, and non-triviality of
  the extended model.
- Not claimed: freshness used by the semantic soundness induction, growing-signature
  allocation, syntactic erasure of a type definition (relativisation), string-name
  lowering, or MoonBit refinement. The later `HistoryDerivation` relation closes the
  fixed-signature history under the supported core inference rules.

## 2026-10-13 Semantics of a type-definition gate

- Added `TypeDefGate` (constructor id, arity with parameters by index, representation
  type, closed predicate, Rep and Abs ids of the total signature) with the side
  conditions `Term.annotVars`-closure over the parameters, `k` not occurring in the
  predicate, `rep ≠ abs`, and `rep`, `abs` not occurring in the predicate. History
  freshness of `k`, `rep` and `abs` is deliberately not a gate field.
- Added the model step `TypeDefGate.interpret`: the new constructor interpretation
  sends `(k, n, as)` to the predicate subtype of the representation type, evaluated in
  the old model with the parameters at `as` and every other variable at `PUnit`, when
  the predicate has a witness there, and to `PUnit` otherwise; the new constants
  interpret `rep` by `Subtype.val` and `abs` by the abstraction of `PredicateWitness`.
  Proved the new constructor interpretation admissible.
- Proved the three laws as valid sequents about Rep and Abs terms in the new model:
  `Abs (Rep a) = a` and `P r ⊢ Rep (Abs r) = r` unconditionally, and `P (Rep a)` under
  the witness hypothesis `TypeDefGate.WitnessAt` (the semantic form of the kernel's
  hypothesis-free witness theorem; `witnessAt_of_valid` discharges it from a valid
  `P w`). A worked pair of gates shows the hypothesis cannot be dropped.
- Proved old-language invariance of the step (`TypeDefGate.valid_iff_old`) for sequents
  mentioning neither `k`, `rep` nor `abs`. It needs locality (`ConstVal.Local`) of the old
  interpretation on the sequent's constants; the canonical interpretation is local.
- Added `Model`, `ModelExtension` (definition, specification and type-definition
  steps over model pairs), `ModelExtension.interpret` and `ModelExtension.valid_iff`
  as a parallel version of `Extension` (the earlier `Extension` with `TypeDefContract`
  is unchanged). The step is now a constructor of `ExtensionDerivation`; locality is
  carried through definition steps, yielding the history-level equivalence theorem.
  The separate `HistoryDerivation` relation now embeds these products and closes them
  under the core rules at a fixed total signature.
## 2026-10-13 Congruence over constructor interpretations

- Added `Ty.tyCons` and `Term.tyCons` (constructor ids occurring in types and in
  binder, variable and constant-instance annotations), `Term.annotVars` (type
  variables in every annotation, including an unused binder's domain), and their
  behaviour under substitution and instantiation.
- Proved `Ty.denote_congr`, `Ty.denote_congr_vars`, the general `Term.eval_congr`
  and its specialisations `Term.eval_congr_κ` and `Term.eval_congr_vars`
  (`HEq` statements). `Term.eval_agree` is now a corollary.
- Added `valid_transport_κ` and `valid_iff_κ`: validity is invariant when the
  constructor interpretation changes on ids the sequent does not mention.
  `valid_transport`, `valid_old_language_iff` and
  `valid_definition_old_language_iff` keep their statements and are derived from
  the general lemmas. The statements need `Admissible` to coincide for the two
  interpretations, and both the hypothesis on the sequent's constructor ids and
  the admissibility hypothesis are shown necessary by an example.
- `Term.typeVars` is unchanged and still omits an unused binder's domain;
  `Term.annotVars` is the support on which evaluation depends. No typedef gate,
  history-indexed interpretation or derivation constructor is added.

## 2026-10-13 Type-constructor nodes and constructor interpretations

- Added `Ty.con k n args` and the constructor interpretation `TyConVal` (default:
  every constructor denotes `PUnit`) to the Lean development. `Ty.denote`,
  `Admissible`, `ConstVal`, evaluation, instantiation, the rules, `Derivation`,
  extension histories and the soundness package are parameterized by it; the core
  theorems hold for every constructor interpretation. No user type constructor or
  typedef semantics is added, and the MoonBit implementation is unchanged.

## 2026-10-12 Detailed mathematical exposition restored

- Restored the original page design, callouts, diagrams, two-part structure,
  named-boundary and scoped-signature discussion, dictionary-passing blueprint,
  and detailed validation appendices. This revision supersedes the condensed
  eight-page rewrite while retaining the Typed HOL-only proof policy.
- Expanded the intrinsic calculus and gave direct mathematical proofs for
  nonempty carriers, renaming, substitution, beta, type instantiation, selector
  coherence, all ten primitive rules, inductive soundness, semantic extension
  contracts, finite validity conservativity, and concrete non-derivability.
- Following Krantz's mathematical-writing guidance, distinguished type contexts
  from assumption lists and named contexts, object equality from meta equality,
  derivability from validity, and semantic interpretations from frontend instance
  stores. Defined type-variable support exactly as in Lean and replaced oversized
  symbolic premises with explicit hypotheses and structured prose.
- Added adjacent Lean source/declaration annotations and a proof trace matrix.
  All 116 distinct referenced names pass Lean `#check`, and their annotated
  source modules were checked. Typst produces a 40-page manuscript; every page
  was rendered and reviewed, including the equations, diagrams, and tables.
- Retained frontend results as explicit proof obligations. Dictionary realization
  starts from schema typing and prerequisite law witnesses rather than assuming
  its own acceptance checks; recursive resolution requires decrease after type
  instantiation. No deleted approximation theorem is used as proof evidence.
- The Lean theorem statements and MoonBit implementation are unchanged by this
  exposition revision. MoonBit refinement, implementation repair for issue #15,
  new type-constructor integration, and syntactic extension erasure remain open.

## 2026-10-12 Typed HOL-only specification rewrite

- Replaced the accumulated implementation-oriented manuscript with a concise
  presentation of the typed calculus, semantics, primitive rules, proof
  dependency, extension contracts, and exact proof boundary.
- Removed all non-HOL Lean modules from `formal_verification/QEDFV`; the retained
  library contains only `QEDFV/HOL` and its public soundness entry point.
- Rewrote the proof plan, conformance guide, audit matrix, and current workspace
  status around the Typed HOL mainline. Historical entries below record prior
  states and are superseded where they describe retained approximate modules or
  the former specification structure.
- Verified the distinction between semantic validity conservativity and
  syntactic derivation erasure; only the former is claimed by the current Lean
  theorem.

## 2026-10-12 Typed HOL mainline and audit status

- Integrated `HOL/Concrete.lean`, `HOL/TypeDefinitions.lean`, `HOL/Definitions.lean`,
  `HOL/Specification.lean`, `HOL/Transport.lean`, `HOL/Conservativity.lean`, and
  the public `HOL/Soundness.lean` entry point into the aggregate Lean target.
- Closed the remaining Typed HOL semantic layer: `HOL/Instantiation.lean` now
  constructs `select_natural`, `HOL/Evaluation.lean` provides a canonical constant
  valuation, and `HOL/Conservativity.lean` proves validity invariance for every
  finite sequence of definition, specification, and typedef interpretations.
  `HOL/Soundness.lean` exposes canonical model existence, extension soundness, and
  the concrete consistency witness for every old-language finite extension.
- Typed HOL now proves constructed carrier non-emptiness, the ten typed rule
  capsules, general open-context `ABS`, exact assumption discharge `DEDUCT`, typed
  `INST_TYPE` and `INST`, and indexed `derivation_sound` with no local `sorry`,
  `axiom`, or `admit` declarations. `select_natural` constructs the required
  choice coherence, and definition/specification gates explicitly record their
  type-variable closure conditions.
- Typed semantic contracts now cover typedef non-emptiness and Abs/Rep laws,
  fresh-constant definition equations, specification validity from a typed witness,
  bidirectional old-language validity invariance for definition/specification
  extensions, finite extension composition, and validity transport for old-language
  sequents under constant agreement. `HOL/Transport.lean` contains the shared
  transport layer.
- `HOL/Concrete.lean` proves a closed `succ 0 = 0` countermodel and non-derivability
  result, giving a typed non-triviality witness.
- Verification: `lake build` passed with **642 jobs**. The axiom scan for all public
  Typed HOL entry points reports only `propext`, `Classical.choice`, and
  `Quot.sound`; the Typed HOL tree contains no local `sorry`, `axiom`, or `admit`.
- The Typed HOL semantic proof is complete. Remaining work is explicitly outside
  this proof scope: distinct-state syntactic erasure, the legacy `Lean.Expr`/MoonBit
  boundary, concrete implementation transfer, and the #15 theorem-provenance bug.

## 2026-10-12 Typed HOL release entry point

- Added `HOL.Soundness.TypedHOLProofPackage`, a single Lean-checked package whose
  fields are all constructed Typed HOL witnesses or theorems: carrier and model
  non-emptiness, renaming/substitution/beta/type-instantiation evaluation laws,
  Choice coherence, derivation soundness, definition/specification/typedef contracts,
  finite semantic conservativity, and concrete consistency.
- Changed the default `QEDFV` target to import only `QEDFV.HOL.Soundness`, so the
  archival `Lean.Expr`/model-law/erasure modules cannot silently serve as proof
  evidence for the Typed HOL mainline.
- The package uses only the standard trusted basis reported by the axiom scan;
  no local `sorry`, `admit`, or custom `axiom` was introduced.

## 2026-10-12 typed HOL semantic core follow-up (historical snapshot)

- Added `formal_verification/QEDFV/HOL/Types.lean`, an intrinsically typed HOL type
  grammar with actual `Prop`, `Nat`, function and variable carriers, plus a
  structural non-emptiness theorem.
- Added `HOL/Terms.lean` and `HOL/Evaluation.lean` for typed De Bruijn terms,
  capture-avoiding substitution, evaluation, and a machine-checked beta law.
- Added `HOL/Extensions.lean` with predicate-subtype carriers, non-emptiness, and
  the three semantic Abs/Rep witness equations used by a typedef contract.
- Added `HOL/Rules.lean` with direct validity-preservation certificates for the
  typed core rules, including the exact assumption-discharge form of DEDUCT and
  term-instantiation validity. The restricted closed-context ABS theorem is named
  accordingly.
- At this earlier checkpoint, polymorphic `INST_TYPE` and general open-context ABS
  were still open. They are closed in the later Typed HOL mainline entry above;
  legacy `Lean.Expr`/MoonBit correspondence remains open.

Verification at that checkpoint: `lake build` passed (633 jobs). The current
verification and axiom basis are recorded in the mainline entry above.

## 2026-10-12 review follow-up (#14, #15, #16)

- Closed the circularity reported in [#14](https://github.com/Luna-Flow/QED/issues/14): `GlobalAdmissibilityEnvelope` is now structural and no longer contains `primitive_sound_all`.
- Recorded the [#15](https://github.com/Luna-Flow/QED/issues/15) forked-state provenance counterexample as an open implementation bug. The Lean pack does not model MoonBit state lineage, so it cannot close this defect by compilation alone.
- Renamed the same-state erasure result to `SEC15_SAME_STATE_ERASURE_FINITE` and made `SEC15_GLOBAL_CONSERVATIVITY_FINITE` a conditional theorem over an explicit `CrossTheoryFiniteErasureObligation`. The obligation's `erases` field is a required simulation conclusion; no theorem in the pack constructs it.
- Replaced the model-class `soundKernel` assumption with an inductive `derivable_sound` proof, and replaced direct implementation derivability assumptions with recursive `CheckedDerivation` evidence. Conditional claims now use `_conditional_proved` or `_structural_proved` theorem names.
- Added fixed matrix statuses (`proved`, `conditional`, `open`, `bug`) and GitHub issue references. The manuscript now labels Construction Invariant, Semantic Non-Triviality, Consistency Witness, and Implementation-to-Logic Transfer with their actual conditional status.
- Corrected the workspace audit language: `lake build` validates the Lean specification/conformance pack, not the MoonBit implementation or a closed model. The current Lean build completes 51 jobs.

### Verification for the review follow-up

- `lake build` in `formal_verification`: passed, 51 jobs.
- `typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-formal-audit.pdf`: passed.
- `moon check`: passed.
- `moon test`: passed, 357/357.
- `lunadoc check . --compile`: passed, 0 errors and 0 warnings; `zh_CN` and `ja_JP` are each 2523/2523 translated.

## 2026-10-12 evidence-driven audit correction

- Added the former `doc/manual/qed_formal_audit_matrices.md` with an issue matrix and a proof-obligation matrix covering the manuscript, Lean formalization, and MoonBit realization. The static matrix was later retired in favor of the generated obligation view.
- Added `formal_verification/QEDFV/Conservativity/CrossTheoryObligations.lean`. It records the missing cross-theory simulation explicitly; it does not assert a proof without that premise.
- Corrected the manuscript's proof-status language for definitional, specification, type-extension, and global conservativity. The previous erasure code keeps one `KernelState`, and its `OldLang` predicate does not inspect the base theory, so it proves same-state tree preservation rather than `T' ⊢ φ -> T ⊢ φ`.
- Marked the current Lean `TypeDefOK`/typedef product contract, `DefOK` theorem shape, `SpecOK` conservativity predicate, abstract boundary laws, and model-law bundles as approximations or conditional obligations. These declarations compile, but they do not by themselves establish the stronger HOL/STT claims in the article.
- Added conformance clarification for the reserved `@` identity and the fact that MoonBit `Thm` stores typed De Bruijn terms at the kernel boundary.

### Verification for this audit

- `lake build` in `formal_verification`: passed, 51 jobs.
- `typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-formal-audit.pdf`: passed.
- `moon check`: passed.
- `moon test`: passed, 357/357.

Remaining open obligations are listed explicitly in the matrices and in the manuscript's proof-status notes; `Open items: None` from earlier rounds no longer applies to the stronger cross-theory and semantic claims.

## Goals and scope of this round

- Goal: finalize the specification so that the structural link between `INST_TYPE` and `DefOK`/`TypeDefOK` is
  explicit at the rule level, and reviewers do not need to read across several sections to see where soundness
  comes from.
- Scope:
  - Consistency sweep of the manuscript (terminology, state model, non-empty type semantics);
  - Rewrite of the `INST_TYPE` rule (premises, failure classification, bridge note);
  - Production of the complete review package (main manuscript + PDF + this changelog).
- Out of scope: changes to the kernel implementation code.

## Section-by-section changes

- `== Global Theory State vs Local Scope State` (`doc/attachments/qed_formal_spec.typ:208`)
  - Makes the two-layer state model `(T, S)` explicit: `T` is the global theory history, `S` is the local poppable
    visibility layer.
  - Adds a proposition stating that `DefHeads(T)` is monotone and that pop does not roll back definition history.
  - Adds an equivalent implementation view: "can be realized as a tombstone registry".

- `== Type Constructor Extension Discipline` (`doc/attachments/qed_formal_spec.typ:257`)
  - Adds the `TypeDefOK` admission condition and rule step for type extensions.
  - Introduces the "no empty-type escape" construction invariant, which turns non-emptiness from a bare assumption
    into an auditable gate constraint.

- `= Definitional Extension Discipline` and `== Definition Admissibility Judgment` (`doc/attachments/qed_formal_spec.typ:694`,
  `doc/attachments/qed_formal_spec.typ:731`)
  - Unifies definition-head novelty as `c ∉ DefHeads(T)` (replacing the ambiguous check against current visibility).
  - Keeps and strengthens `TVars(r) ⊆ TVars(tau)` as a normative condition, which continues to close the ghost-type
    loophole.

- `= Global Admissibility Envelope` (`doc/attachments/qed_formal_spec.typ:763`)
  - Extends the envelope: in addition to `DefOK`, adds `TypeDefOK` as a required gate for type extensions.

- `== Rule Schema: INST_TYPE` (`doc/attachments/qed_formal_spec.typ:1052`)
  - Rewrites the generic `valid(theta)` into structured premises:
    - `valid_ty_subst(theta)`;
    - `admissible_ty_image(T, theta)`;
    - `def_inst_coherent(theta, A_p ⊢ p)`.
  - Extends the failure classification to 5 entries, each corresponding one-to-one to the premises above.
  - Adds a Bridge Note that states explicitly how the rule closes the loop with `DefOK`/`TypeDefOK`/Global Envelope.

- `== Signatures and Symbols` / `== Constant Type Schemes and Instance Relation` (`doc/attachments/qed_formal_spec.typ:104`)
  - Introduces the principal type scheme of constants `kappa_c : tau_gen` and the instance relation
    `tau preceq tau_gen`.
  - States that constant instantiation is a first-class relation at the specification level; the "type in the term
    == registered type" literal identity is no longer required.

- `== Core Typing over Resolved Terms` (`doc/attachments/qed_formal_spec.typ:372`)
  - Changes the `RConst` rule from "exact type equality" matching to "principal scheme + instance relation"
    matching.
  - Adds a lemma on the availability of polymorphic constant instantiation, stating that the system is not locked
    into monomorphism.

- `= Soundness Strategy` and the dependency graph (`doc/attachments/qed_formal_spec.typ:1132`, `doc/attachments/qed_formal_spec.typ:1152`)
  - Extends the obligations from 4 to 5, with "type-level non-emptiness preservation" listed separately.
  - Adds the nodes `Type Admissibility + TypeDefOK` and `Type Non-Emptiness Preservation` to the dependency graph.

- `== Semantic Assumptions` (`doc/attachments/qed_formal_spec.typ:1190`)
  - Narrows "all types are non-empty" from a single global assumption to:
    - a non-emptiness assumption for the base prelude;
    - a global non-emptiness preservation theorem under the `TypeDefOK` premise.

- Appendix updates (from `doc/attachments/qed_formal_spec.typ:1301` onward)
  - Appendix A: `INST_TYPE` dependencies now include `TypeDefOK` and definitional coherence.
  - Appendix B: check items now cover the type gate and the separation of state history.
  - Appendix C: extended to Definition + State scenarios, with a pop-then-redefine rejection case.
  - Appendix D: adds type soundness audit scenarios.

## Audit issue matrix (Issue -> Fix -> Location -> Residual Risk)

| Issue | Fix | Location | Residual Risk |
|---|---|---|---|
| Ghost Type Variable (free type variables escaping from a definition body) | Enforce `TVars(r) ⊆ TVars(tau)` + `INST_TYPE` Bridge Note + `def_inst_coherent` premise | `doc/attachments/qed_formal_spec.typ:701`, `doc/attachments/qed_formal_spec.typ:1052` | Low (the implementation must still enforce exactly the same condition) |
| Empty Type Semantic Escape (semantic escape through empty types) | Add `TypeDefOK` + non-emptiness witness gate + non-emptiness preservation theorem | `doc/attachments/qed_formal_spec.typ:257`, `doc/attachments/qed_formal_spec.typ:1190` | Low to medium (future extensions of typedef syntax must keep the witness rule) |
| Stack vs Theory inconsistency (ambiguous redefinition after pop) | Separate `(T,S)`; bind definition-head novelty to `DefHeads(T)`; pop does not roll back history | `doc/attachments/qed_formal_spec.typ:208`, `doc/attachments/qed_formal_spec.typ:694` | Low (the UI layer must still show kernel identities to avoid symbol confusion) |
| `INST_TYPE` not traceable in review (requires guessing across chapters) | Add explicit admissibility anchors and failure mapping inside the rule | `doc/attachments/qed_formal_spec.typ:1052` | Low |
| De Bruijn Type Erasure (type erasure at the kernel level) | Change the De Bruijn core syntax to carry explicit type labels (`DAbs(tau, ...)`, `DBound(..., tau)`), and change the `TRANS`/`BETA` matching conditions to typed-core guards | `doc/attachments/qed_formal_spec.typ:439`, `doc/attachments/qed_formal_spec.typ:886`, `doc/attachments/qed_formal_spec.typ:977` | Low (the implementation must strictly preserve type labels during boundary lowering) |
| Polymorphism Lockout (polymorphic constant instantiation locked out) | Introduce principal schemes for constants and the instance relation `tau ≼ tau_gen`, and add instance guards to elaboration, core typing and `INST_TYPE` | `doc/attachments/qed_formal_spec.typ:125`, `doc/attachments/qed_formal_spec.typ:379`, `doc/attachments/qed_formal_spec.typ:1109` | Low (the implementation must use the same instance judgment) |

## Incremental revision (De Bruijn type erasure audit)

- `== De Bruijn Shifting (for BETA)` (`doc/attachments/qed_formal_spec.typ:439`)
  - Replaces the untyped constructors (`Abs(t)`, `BVar(k)`) with typed core constructors (`DAbs(tau, t)`,
    `DBound(k, tau)`).
  - Adds a binder/argument type agreement side condition to the `beta` contraction rule.
  - Adds a typed-core injectivity invariant that prevents abstractions over different domain types from being
    structurally identified.

- `== Boundary Conversion Properties` (`doc/attachments/qed_formal_spec.typ:510`)
  - Adds the Type-Sensitive Core Matching lemma, stating that boundary lowering does not erase binder-domain type
    labels.

- `== Rule Schema: TRANS` (`doc/attachments/qed_formal_spec.typ:865`)
  - Adds a typed De Bruijn core matching premise and the corresponding failure entry, which prevents middle terms
    from being mismatched by their "erased structure".

- `== Rule Schema: BETA` (`doc/attachments/qed_formal_spec.typ:954`)
  - Rewrites the redex shape into its typed version;
  - Adds binder-domain label mismatch to the failure classification;
  - The antecedent form now explicitly includes `type_of(u) = tau`.

- Appendix enhancements:
  - Appendix A adds the typed-core dependencies of `TRANS`/`BETA`;
  - Appendix B adds a check item for type-sensitive De Bruijn matching;
  - Adds Appendix E (Typed De Bruijn Core Audit Scenarios).

## Incremental revision (Polymorphism Lockout audit)

- `== Constant Type Schemes and Instance Relation`
  - Adds the principal scheme of constants `kappa_c : tau_gen` and the instance relation `tau ≼ tau_gen`.
  - States that a constant is valid in the core as "principal scheme + instantiated type"; literal type equality is
    no longer required.

- `== Named Elaboration Judgment` and `== Core Typing over Resolved Terms`
  - The elaboration and core typing premises of `RConst` both switch to the instance-relation judgment.
  - Adds the "Polymorphic Constant Instantiation Admissibility" lemma and a "No Monomorphic Lockout" remark.

- `== Rule Schema: INST_TYPE`
  - Adds a constant-instance consistency side condition: `tau_i ≼ tau_gen(kappa_c)`.
  - Adds constant-instance mismatch to the failure classification.
  - The Bridge Note now covers the constant-instance guard and expressiveness.

- Appendix enhancements:
  - Appendix A adds the dependency of `INST_TYPE` on the constant instance relation;
  - Appendix B adds a `tau ≼ tau_gen` check item;
  - Appendix D adds a polymorphic constant instantiation audit scenario (`id` usable at the `bool/int` instances).

## Acceptance checklist (with pass/fail)

- [PASS] The `INST_TYPE` section explicitly references `DefOK`, `TypeDefOK` and the Global Admissibility Envelope.
- [PASS] Global history semantics is unified as `DefHeads(T)` and separated from local `pop` behavior.
- [PASS] Non-empty type semantics moves from a bare assumption to the `TypeDefOK` gate + preservation theorem
  narrative.
- [PASS] The manuscript appendices include Ghost/Empty/Pop-Redefine regression scenarios.
- [PASS] The De Bruijn core carries explicit type annotations, and the `TRANS`/`BETA` rules enforce checks on them.
- [PASS] Polymorphic constant use is enabled through the `tau preceq tau_gen` instance relation, avoiding
  monomorphic lockout.
- [PASS] The compilation check passes:
  - Command: `typst compile doc/qed_formal_spec.typ doc/qed_formal_spec.pdf`
  - Result: [QED formal specification](../attachments/qed_formal_spec.typ) is generated successfully.

## Open items (status at the time of that revision)

None was recorded for the manuscript-editing scope of that revision. The 2026-10-12 audit supersedes that status for proof claims: cross-theory conservativity, semantic model construction, concrete boundary refinement, and the exact typedef/specification obligations remain open as documented above.

## Incremental revision (constructive closure)

- Upgrades the *Theorem Goal* in the `SpecOK` section to a formal theorem, and adds a constructive proof method for
  "single-step spec head elimination":
  - defines the recursive eliminator `erase_spec` within the manuscript;
  - gives a well-founded induction invariant based on derivation tree size.
- Adds the `Constructive Closure: Derivation Objects and Erasure Operators` section:
  - introduces finite derivation objects `Derives(D, s)`;
  - defines three kinds of eliminators: `erase_def` / `erase_spec` / `erase_typedef`;
  - gives three corresponding correctness theorems (preservation of old-language sentences).
- Upgrades `Meta-Theorem Target` to a formal global conservativity meta-theorem:
  - writes out explicitly the compositional proof by step-by-step back-erasure over finite extension sequences;
  - derives the global `T' ⊢ φ => T ⊢ φ` from the correctness of each per-step gate elimination.
- Updates the document status and the P0 checklist accordingly:
  - `Current Status` now reads "constructive closure is given in the manuscript";
  - the checklist adds two items: "derivation object system" and "per-gate elimination + composition theorem".

## Incremental revision (two-part split and authority boundary)

- Adds `Part I: Logic Core (Normative)` and an *Authority Contract* at the front of the main manuscript:
  - states that Part I is the sole normative source for the logic;
  - states that De Bruijn and scope are mechanisms of logical correctness, not optional engineering details.
- Renames the entry of the engineering part to
  `Part II: Engineering Realization (Informative + Conformance)`:
  - declares explicitly that Part II is downstream of Part I and must not define the logic in reverse.
- Adds the `Conformance Obligations (Part I -> Part II)` subsection:
  - five implementation conformance obligations: rule fidelity, boundary fidelity, scope stability, gate fidelity
    and certificate non-authority.
- Rewrites the first sentence of `Documentation Maintenance Notes` to reflect the two-part maintenance approach:
  - Part I is maintained as the source of truth for the logic;
  - Part II is maintained as the conformance-report layer for Part I.

## Incremental revision (strengthened De Bruijn / scope proofs)

- Adds three bridge theorems to the De Bruijn section:
  - `Lowering Preserves Typing`;
  - `Lifting Preserves Typing up to Alpha`;
  - `Boundary Commutation with Capture-Avoiding Substitution`.
- Turns the three scoped shadowing propositions from proof sketches into full proofs (derived step by step from the
  definitions).
- Adds the `Resolution Freeze under Scope Mutation` theorem:
  - formally states that the premises of already-resolved terms are invariant under subsequent `push/add/pop`
    sequences;
  - states that scope only affects future name resolution and does not write back to existing resolved objects.

## Incremental revision (automatic phase advance: de-engineering Part I + converging Part II)

- Removes engineering ties from the wording of Part I (without changing the logical content):
  - the Abstract changes from "implementation-aware specification" to "formal mathematical specification";
  - "In implementation terms" in `Type Grammar` / `Term Grammar` is rewritten as "One canonical concrete
    representation";
  - API/implementation wording in the boundary/scope paragraphs is rewritten as abstract semantic wording (still
    implementable, but not tied to any particular implementation).
- Upgrades the `MK_COMB` section from `Type Preservation Sketch` to `Type Preservation Theorem`:
  - keeps the original derivation structure and completes it in the full "Proof." closing style.
- Converges Part II to conformance semantics:
  - the error taxonomy alignment paragraph changes from "normative for final API" to "conformance target for
    engineering realizations";
  - the closing sentence of Appendix B changes to "logic-closure + conformance/regression gate".

## Incremental revision (automatic phase advance: Part II conformance closure)

- Adds an "informative only" boundary statement to `Engineering Correspondence`:
  - the module mapping serves only audit coverage and does not change any definition or theorem of Part I.
- Adds the `Conformance Transfer Theorem` section:
  - defines `Faithful Realization` (satisfying the five conformance obligations);
  - gives the transfer theorem from implementation to logic: if the implementation accepts sequent $s$, then $s$ is
    derivable in Part I;
  - the proof reconstructs the acceptance trace: rule mapping, substitution by boundary lemmas, erasure via scope
    stability, gate correspondence and discarding of certificate events.
- Removes implementation coupling from the introductory paragraph of Primitive Rules:
  - changes "parallel with implementation updates" to "Part I side conditions are authoritative".

## Incremental revision (automatic phase advance: strengthened constructive closure for Primitive Rules)

- Adds `Rule-Level Constructive Preservation Capsules` at the end of the `Rule Schema` chapter:
  - gives a uniform constructive template `Preserve_R : valid(Premises_R) => valid(Conclusion_R)`;
  - gives an encapsulated preservation statement for each of the 10 primitive rules (including the three
    constraints of `INST_TYPE`: gate, coherence and instance);
  - adds the summary theorem `Rule Capsule Closure`, stating that "per-rule case analysis + capsule invocation" is
    enough to close the P1 obligation.

## Incremental revision (automatic phase advance: closing the two-part audit checklist)

- Extends Appendix B (P0 checklist) with Part II consistency items:
  - adds items 24-28, covering the Part II downstream declaration, the five conformance obligations, the transfer
    theorem, the non-authoritative mapping and the conformance positioning of the error taxonomy.
- Adds Appendix G `Part II Conformance Audit Scenarios`:
  - Rule-fidelity replay;
  - Boundary-fidelity;
  - Scope-fidelity stability;
  - Gate-fidelity;
  - Certificate non-authority.
- This completes the two-level audit structure of "Part I logic closure + Part II conformance closure".

## Incremental revision (automatic phase advance: semantic assumption package and consistency layer)

- Adds a model-class wrapper under `Semantic Assumptions`:
  - adds the `Admissible Model Class` definition (typing/denotation + Choice + Infinity anchor + gate-admitted
    theorems).
  - adds the `Model-Class Non-Emptiness` assumption, making the "a non-trivial model exists" premise explicit.
- Adds consistency transfer results:
  - `Semantic Non-Triviality Transfer` (a countermodel implies non-derivability);
  - `Consistency Witness Form` (under the semantics of the same model class, a sentence and its negation are not
    both derivable).

## Incremental revision (automatic phase advance: claim-to-proof trace matrix)

- Adds Appendix H `Claim-to-Proof Trace Matrix`:
  - gives short-path mappings from ten high-level claims C1..C10 to "definition anchor/proof anchor";
  - covers rule soundness, conservativity of the three gate kinds, scope/boundary stability, global
    conservativity, conformance transfer, non-triviality and certificate non-authority.
- Adds a review rule at the end of the appendix:
  - each claim aims to be reachable in three steps, "claim -> definition -> theorem", to ease review and
    cross-checking.

## Incremental revision (automatic phase advance: terminology consistency refinement)

- Further removes engineering terms from Part I and unifies them:
  - `external modules` becomes `external contexts`;
  - `implementation-level check` becomes `admission-procedure check`;
  - `module boundaries and test responsibilities` is rewritten from a proof-block perspective;
  - the word `implementation` at the infinity anchor and the canonical theorems is replaced with
    realization/presentation semantics.
- Unifies the wording of the maintenance notes and audit scenarios accordingly:
  - `APIs evolve` becomes `realization interfaces evolve`;
  - the schema widening scenario in Appendix F now uses admission-procedure semantics.
- Unifies notation:
  - the semantic interpretation notation is unified as `"denote"(t, rho, M)`, using the same parameter convention
    as the later boundary denotation lemmas.

## Incremental revision (automatic phase advance: filling in closure anchors)

- Adds the missing definition anchors to `Audit Certificates and Replay Interface` in Part II:
  - adds the `Admissible(T, t_h)` definition (witnessed by Part I `Derives` objects and gate legality);
  - adds the `SentenceInLanguage(T_0, t_h)` definition (closed sentence + base language symbol constraint).
- `ConservativeReplayOK` now uses explicitly defined predicates and no longer relies on implicit semantic
  premises.

## Incremental revision (notation consistency fix)

- Makes the slash notation in substitutions consistent:
  - unifies `t[s/x]` as `t[s\/x]`;
  - matches the existing `s[u\/x]` notation in the text, avoiding ambiguity of the `[A/B]` form in review and
    rendering.

## Incremental revision (tone refinement)

- Moves the tone of the whole text toward an academic paper style, without changing the logical content:
  - `Authority Contract` becomes `Normative Scope`, and some strongly imperative sentences are rewritten as
    academic expository sentences;
  - the opening of Part II shifts from "implementation hooks" framing to "concrete realization and conformance
    record" framing;
  - `Documentation Maintenance Notes` becomes `Concluding Remarks`, and `Near-term maintenance focus` becomes
    `Future refinement directions`.
- Unifies the tone of the appendices:
  - `Audit Scenarios` is uniformly renamed `Validation Scenarios`;
  - the ending changes from "required before claiming" to "provide structured evidence for ...".
- Detailed semantic consistency:
  - the semantic interpretation notation is unified as `"denote"(t, rho, M)` (consistent with the later
    denotation lemmas);
  - the predicates related to `ConservativeReplayOK` are now defined by name in the text, reducing implicit
    terminology.
