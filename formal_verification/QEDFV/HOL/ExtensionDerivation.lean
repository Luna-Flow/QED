import QEDFV.HOL.ModelExtension

namespace QEDFV.HOL

/-! Derivations indexed by the declaration history in which they are used. The head of a
history is its newest step.

The history type is `List (ModelExtension S)`, the model-pair version of the declaration
steps (definition, specification, **type definition**). The earlier `Extension κ S` is indexed
by one fixed constructor interpretation `κ`, but a type-definition step changes `κ`: it cannot
be an endomorphism of `ConstVal κ S`. Hence histories are interpreted over a `Model`
(`interpretModels`) and soundness returns validity at the history's *model pair*. -/

/-- Which of the three laws of a type definition a derivation concludes. -/
inductive TypeDefLaw where
  /-- `⊢ Abs (Rep a) = a` -/
  | absRep
  /-- `⊢ P (Rep a)` -/
  | repRange
  /-- `P r ⊢ Rep (Abs r) = r` -/
  | repAbs

/-- The context of the sequent of a law. -/
def TypeDefLaw.ctx {S : Signature} (G : TypeDefGate S) : TypeDefLaw → List Ty
  | .absRep => [G.newTy]
  | .repRange => [G.newTy]
  | .repAbs => [G.repTy]

/-- The sequent of a law: the selector of the single typedef derivation constructor. -/
def TypeDefLaw.sequent {S : Signature} (G : TypeDefGate S) :
    (l : TypeDefLaw) → Sequent S (l.ctx G)
  | .absRep => G.absRepSequent
  | .repRange => G.repRangeSequent
  | .repAbs => G.repAbsSequent

/-- The three laws hold in the model after a type-definition step, given a witness of the
predicate at the old model (the semantic form of the witness derivation). -/
theorem TypeDefGate.valid_law {S : Signature} (G : TypeDefGate S) (M : Model S)
    (hloc : G.PredLocal M.I) (hW : G.WitnessAt M.I) (l : TypeDefLaw) :
    Valid (G.interpret M).I (l.sequent G) := by
  cases l with
  | absRep => exact G.valid_absRep M.adm M.I
  | repRange => exact G.valid_repRange M.adm M.I hloc hW
  | repAbs => exact G.valid_repAbs M.adm M.I hloc

/-- The derivation relation. `core` embeds the pure calculus, `weaken` lifts a derivation
across a newer step for sequents in that step's old language (no mention of its constants or
type constructors), and `definition`, `specification` and `typedef` introduce the theorems of
the corresponding kernel steps.

`typedef` is one constructor with a three-valued selector `l`; its premise `d` is the
mandatory witness derivation `⊢ P w` (hypothesis-free, closed `w`) at the preceding history,
as the kernel requires. History freshness of `k`, `rep` and `abs` is a carried side condition
(like the freshness premises of `definition` and `specification`): soundness does not use
it, well-formed histories do. -/
inductive ExtensionDerivation (S : Signature) :
    List (ModelExtension S) → {Γ : List Ty} → Sequent S Γ → Prop where
  | core {es Γ} {s : Sequent S Γ} (d : Derivation S s) :
      ExtensionDerivation S es s
  | weaken {es Γ} {s : Sequent S Γ} (e : ModelExtension S)
      (d : ExtensionDerivation S es s) (hOld : e.oldLanguage s) :
      ExtensionDerivation S (e :: es) s
  | definition {es} (D : DefinitionGate S)
      (hFresh : D.id ∉ modelHistoryIds es) :
      ExtensionDerivation S (.definition D :: es)
        { hyps := [], concl := D.head.equal D.rhs }
  | specification {es} (E : SpecificationExtension S)
      (hFresh : E.gate.id ∉ modelHistoryIds es)
      (d : ExtensionDerivation S es { hyps := [], concl := E.gate.body }) :
      ExtensionDerivation S (.specification E :: es)
        { hyps := [], concl := E.gate.predicate.substitute
            (Sub.single (E.gate.constant E.typeEq)) }
  | typedef {es} (G : TypeDefGate S) (l : TypeDefLaw)
      (hk : G.k ∉ modelHistoryTyCons es) (hrep : G.rep ∉ modelHistoryIds es)
      (habs : G.abs ∉ modelHistoryIds es) (w : Term S [] G.repTy)
      (d : ExtensionDerivation S es { hyps := [], concl := G.pred.app w }) :
      ExtensionDerivation S (.typeDefinition G :: es) (l.sequent G)

/-- **Soundness of history-indexed derivations at the history's model pair.** For a local
base model `M` (the canonical model is local), a derivation at the history `es` is valid in
the model pair `interpretModels es M`, constructor interpretation included.

The `typedef` case discharges `WitnessAt` from the witness derivation via the induction
hypothesis and `TypeDefGate.witnessAt_of_valid`; the `weaken` case for a type-definition step
uses old-language transport (`TypeDefGate.valid_iff_old`), whose locality hypothesis is
supplied by `interpretModels_isLocal`. -/
theorem extension_derivation_sound (M : Model S) (hM : M.IsLocal)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) :
    Valid (interpretModels es M).I s := by
  induction d with
  | core d =>
      exact derivation_sound select_natural (interpretModels _ M).I d
  | weaken e d hOld ih =>
      change Valid (e.interpret (interpretModels _ M)).I _
      exact (e.valid_iff (interpretModels _ M) _ hOld
        fun c _ ↦ interpretModels_isLocal _ hM c).2 ih
  | @definition es D hFresh =>
      exact valid_definition_equation D (interpretModels es M).I
        (fun c ↦ interpretModels_isLocal _ hM c)
  | specification E hFresh d ih =>
      exact E.valid_gate (interpretModels _ M).I (fun c ↦ interpretModels_isLocal _ hM c) ih
  | typedef G l hk hrep habs w d ih =>
      exact G.valid_law (interpretModels _ M)
        (fun c _ ↦ interpretModels_isLocal _ hM c) (G.witnessAt_of_valid _ w ih) l

/-- Soundness over the canonical model of an admissible constructor interpretation. -/
theorem typed_extension_derivation_sound {κ : TyConVal} (hκ : κ.IsAdmissible)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) :
    Valid (interpretModels es (Model.canonical hκ S)).I s :=
  extension_derivation_sound (Model.canonical hκ S) (Model.canonical_isLocal hκ S) d

/-- Soundness over the default model (every base constructor denotes `PUnit`). -/
theorem typed_extension_derivation_sound_default
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) :
    Valid (interpretModels es (Model.default S)).I s :=
  typed_extension_derivation_sound defaultTyCon_isAdmissible d

/-- **Derivation-level conservativity.** A sequent derivable at a history that mentions none
of the constants and type constructors the history introduces is valid at the canonical base
model: derivations at a history prove nothing new about the old language, semantically. -/
theorem extension_derivation_old_language_valid {κ : TyConVal} (hκ : κ.IsAdmissible)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) (hOld : oldLanguageModels es s) :
    Valid (canonicalConstVal κ S) s :=
  (typed_global_semantic_conservativity_models hκ es s hOld).1
    (typed_extension_derivation_sound hκ d)

end QEDFV.HOL
