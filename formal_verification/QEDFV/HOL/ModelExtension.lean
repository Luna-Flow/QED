import QEDFV.HOL.Conservativity
import QEDFV.HOL.TypeDefLocal

/-! Extension steps on a model pair `(κ, I)`. The step of a type definition changes the
constructor interpretation `κ`, so it cannot be an endomorphism of `ConstVal κ S`; this file
adds a model-pair version of `Extension` and `Extension.interpret`; `ExtensionDerivation` is
indexed by histories of these steps. The earlier `Extension κ S` (with its carrier-level
`TypeDefContract`) is unchanged and remains for the type-definition-free finite statement. -/
namespace QEDFV.HOL

/-- A model: an admissible constructor interpretation and a constant interpretation. -/
structure Model (S : Signature) where
  κ : TyConVal
  adm : κ.IsAdmissible
  I : ConstVal κ S

/-- The model pair after a type-definition step. -/
noncomputable def TypeDefGate.interpret {S : Signature} (G : TypeDefGate S) (M : Model S) :
    Model S :=
  { κ := G.newTyCon M.I
  , adm := G.newTyCon_isAdmissible M.adm M.I
  , I := G.newConst M.adm M.I }

/-- Declaration steps over model pairs. -/
inductive ModelExtension (S : Signature) where
  | definition (gate : DefinitionGate S)
  | specification (extension : SpecificationExtension S)
  | typeDefinition (gate : TypeDefGate S)

/-- The constant ids a step introduces. -/
def ModelExtension.constantIds {S : Signature} : ModelExtension S → Finset Nat
  | .definition D => {D.id}
  | .specification E => {E.gate.id}
  | .typeDefinition G => {G.rep, G.abs}

/-- The type-constructor ids a step introduces. -/
def ModelExtension.tyConIds {S : Signature} : ModelExtension S → Set Nat
  | .definition _ => ∅
  | .specification _ => ∅
  | .typeDefinition G => {G.k}

/-- A sequent is in the old language of a step when it mentions none of the step's new
constants and type constructors. -/
def ModelExtension.oldLanguage {S : Signature} {Γ : List Ty} :
    ModelExtension S → Sequent S Γ → Prop
  | .definition D, s => D.id ∉ s.constIds
  | .specification E, s => E.gate.id ∉ s.constIds
  | .typeDefinition G, s => G.k ∉ s.tyCons ∧ G.rep ∉ s.constIds ∧ G.abs ∉ s.constIds

/-- The model after a step. Definition and specification steps keep `κ`. -/
noncomputable def ModelExtension.interpret {S : Signature} :
    ModelExtension S → Model S → Model S
  | .definition D, M => { M with I := M.I.withDefinition D }
  | .specification E, M => { M with I := M.I.withSpecification E.gate E.typeEq }
  | .typeDefinition G, M => G.interpret M

/-- Declaration steps, newest first, interpreted over a model pair. -/
noncomputable def interpretModels {S : Signature} :
    List (ModelExtension S) → Model S → Model S
  | [], M => M
  | e :: rest, M => e.interpret (interpretModels rest M)

/-- Old-language invariance of one step. Locality of the old constants of the sequent is only
used by the type-definition step (see `TypeDefGate.valid_iff_old`). -/
theorem ModelExtension.valid_iff {S : Signature} {Γ : List Ty} (e : ModelExtension S)
    (M : Model S) (s : Sequent S Γ) (hOld : e.oldLanguage s)
    (hloc : ∀ c, c ∈ s.constIds → M.I.Local c) :
    Valid (e.interpret M).I s ↔ Valid M.I s := by
  cases e with
  | definition D => exact valid_definition_old_language_iff D M.I s hOld
  | specification E => exact E.gate.valid_old_language_iff M.I E.typeEq s hOld
  | typeDefinition G => exact G.valid_iff_old M.adm M.I s hOld.1 hOld.2.1 hOld.2.2 hloc

/-- **The three type-definition laws in the model after a gate step.** With `P` the gate's
predicate, `Rep`/`Abs` the two new constants:
* `Abs (Rep a) = a` is valid unconditionally;
* `P (Rep a)` is valid provided the predicate has a witness at every admissible valuation of
  the old model (`TypeDefGate.WitnessAt`, the semantic form of the kernel's hypothesis-free
  witness theorem `⊢ P w`; see `TypeDefGate.witnessAt_of_valid`);
* `P r ⊢ Rep (Abs r) = r` is valid unconditionally (the premise `P r` is itself a witness).
Locality of the predicate's constants (`TypeDefGate.PredLocal`) lets the new model read the
predicate off the old one. -/
theorem TypeDefGate.laws {S : Signature} (G : TypeDefGate S) (M : Model S)
    (hloc : G.PredLocal M.I) (hW : G.WitnessAt M.I) :
    Valid (G.interpret M).I G.absRepSequent ∧ Valid (G.interpret M).I G.repRangeSequent ∧
      Valid (G.interpret M).I G.repAbsSequent :=
  ⟨G.valid_absRep M.adm M.I, G.valid_repRange M.adm M.I hloc hW, G.valid_repAbs M.adm M.I hloc⟩

/-- The laws from a hypothesis-free derivation-style witness `⊢ P w` valid in the old model
(this is the statement `extension_derivation_sound` instantiates for the `typedef` constructor). -/
theorem TypeDefGate.laws_of_witness_valid {S : Signature} (G : TypeDefGate S) (M : Model S)
    (hloc : G.PredLocal M.I) (w : Term S [] G.repTy)
    (hw : Valid M.I { hyps := [], concl := G.pred.app w }) :
    Valid (G.interpret M).I G.absRepSequent ∧ Valid (G.interpret M).I G.repRangeSequent ∧
      Valid (G.interpret M).I G.repAbsSequent :=
  G.laws M hloc (G.witnessAt_of_valid M.I w hw)

/-- The canonical constant interpretation is local. -/
theorem canonicalConstVal_local (κ : TyConVal) (S : Signature) (c : Nat) :
    (canonicalConstVal κ S).Local c := by
  intro ρ hρ ρ' hρ' h
  have e : (S c).denote κ ρ = (S c).denote κ ρ' := (S c).denote_congr_vars κ h
  exact heq_choice _ _ e

/-- Over the canonical constant interpretation, old-language invariance of a type-definition
step needs no locality hypothesis. -/
theorem TypeDefGate.valid_iff_old_canonical {S : Signature} (G : TypeDefGate S) {κ : TyConVal}
    (hκ : κ.IsAdmissible) {Γ : List Ty} (s : Sequent S Γ) (hk : G.k ∉ s.tyCons)
    (hr : G.rep ∉ s.constIds) (ha : G.abs ∉ s.constIds) :
    Valid (G.newConst hκ (canonicalConstVal κ S)) s ↔ Valid (canonicalConstVal κ S) s :=
  G.valid_iff_old hκ _ s hk hr ha fun c _ ↦ canonicalConstVal_local κ S c


/-! ### Locality and old-language invariance along a history -/

/-- Every constant of the model is interpreted locally (`ConstVal.Local`). This is the
semantic invariant the soundness induction carries along a history: a type-definition step
needs it (`TypeDefGate.valid_iff_old`), and every step preserves it. -/
def Model.IsLocal {S : Signature} (M : Model S) : Prop := ∀ c, M.I.Local c

/-- The canonical model of an admissible constructor interpretation. -/
noncomputable def Model.canonical {κ : TyConVal} (hκ : κ.IsAdmissible) (S : Signature) :
    Model S :=
  { κ := κ, adm := hκ, I := canonicalConstVal κ S }

/-- The canonical model over the default constructor interpretation (every constructor
denotes `PUnit`). -/
noncomputable def Model.default (S : Signature) : Model S :=
  Model.canonical defaultTyCon_isAdmissible S

theorem Model.canonical_isLocal {κ : TyConVal} (hκ : κ.IsAdmissible) (S : Signature) :
    (Model.canonical hκ S).IsLocal :=
  canonicalConstVal_local κ S

/-- **Every declaration step preserves locality.** For a definition or a specification this is
the `annotVars` closure field of the gate; for a type definition it is
`TypeDefGate.newConst_local`. -/
theorem ModelExtension.interpret_isLocal {S : Signature} (e : ModelExtension S) {M : Model S}
    (hM : M.IsLocal) : (e.interpret M).IsLocal := by
  cases e with
  | definition D => exact D.withDefinition_local M.I hM
  | specification E => exact E.gate.withSpecification_local M.I E.typeEq hM
  | typeDefinition G => exact G.newConst_local M.adm M.I hM

theorem interpretModels_isLocal {S : Signature} (es : List (ModelExtension S)) {M : Model S}
    (hM : M.IsLocal) : (interpretModels es M).IsLocal := by
  induction es with
  | nil => exact hM
  | cons e rest ih => exact e.interpret_isLocal ih

/-- The constant ids introduced anywhere in a history. -/
def modelHistoryIds {S : Signature} (es : List (ModelExtension S)) : Finset Nat :=
  es.foldr (fun e ids ↦ e.constantIds ∪ ids) ∅

/-- The type-constructor ids introduced anywhere in a history. -/
def modelHistoryTyCons {S : Signature} (es : List (ModelExtension S)) : Set Nat :=
  {k | ∃ e, e ∈ es ∧ k ∈ e.tyConIds}

/-- A sequent is in the old language of a history when it is in the old language of every
step of it. -/
def oldLanguageModels {S : Signature} {Γ : List Ty} (es : List (ModelExtension S))
    (s : Sequent S Γ) : Prop :=
  ∀ e, e ∈ es → e.oldLanguage s

/-- **Old-language invariance along a history with type definitions.** If the base model is
local, a sequent mentioning none of the constants and type constructors a history introduces
is valid at the history's model pair iff it is valid at the base model. -/
theorem valid_interpretModels_iff {S : Signature} {Γ : List Ty} (es : List (ModelExtension S))
    (M : Model S) (hM : M.IsLocal) (s : Sequent S Γ) (hOld : oldLanguageModels es s) :
    Valid (interpretModels es M).I s ↔ Valid M.I s := by
  induction es with
  | nil => exact Iff.rfl
  | cons e rest ih =>
      have hRest : oldLanguageModels rest s := fun e' he' ↦ hOld e' (List.mem_cons_of_mem _ he')
      change Valid (e.interpret (interpretModels rest M)).I s ↔ Valid M.I s
      rw [e.valid_iff (interpretModels rest M) s (hOld e (List.mem_cons_self ..))
        fun c _ ↦ interpretModels_isLocal rest hM c]
      exact ih hRest

/-- The statement of `typed_global_semantic_conservativity` for histories that include
type-definition entries, over the canonical model of any admissible constructor
interpretation. No locality hypothesis remains: the canonical model is local. -/
theorem typed_global_semantic_conservativity_models {κ : TyConVal} (hκ : κ.IsAdmissible)
    {S : Signature} {Γ : List Ty} (es : List (ModelExtension S)) (s : Sequent S Γ)
    (hOld : oldLanguageModels es s) :
    Valid (interpretModels es (Model.canonical hκ S)).I s ↔ Valid (canonicalConstVal κ S) s :=
  valid_interpretModels_iff es (Model.canonical hκ S) (Model.canonical_isLocal hκ S) s hOld

end QEDFV.HOL
