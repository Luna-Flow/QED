import QEDFV.HOL.Conservativity
import QEDFV.HOL.TypeDefGate

/-! Extension steps on a model pair `(κ, I)`. The step of a type definition changes the
constructor interpretation `κ`, so it cannot be an endomorphism of `ConstVal κ S`; this file
adds a parallel, model-pair version of `Extension` and `Extension.interpret`. The earlier
`Extension κ S` (with its carrier-level `TypeDefContract`) is unchanged. -/
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
(this is the statement PR 4 instantiates with `extension_derivation_sound`). -/
theorem TypeDefGate.laws_of_witness_valid {S : Signature} (G : TypeDefGate S) (M : Model S)
    (hloc : G.PredLocal M.I) (w : Term S [] G.repTy)
    (hw : Valid M.I { hyps := [], concl := G.pred.app w }) :
    Valid (G.interpret M).I G.absRepSequent ∧ Valid (G.interpret M).I G.repRangeSequent ∧
      Valid (G.interpret M).I G.repAbsSequent :=
  G.laws M hloc (G.witnessAt_of_valid M.I w hw)

theorem heq_choice {A B : Type} (hA : Nonempty A) (hB : Nonempty B) (h : A = B) :
    HEq (Classical.choice hA) (Classical.choice hB) := by
  subst h
  rfl

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

end QEDFV.HOL
