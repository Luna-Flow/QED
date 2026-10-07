# Formal specification changelog

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

## Open items (write None if there are none)

None.

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
