import QEDFV.HOL.ExtensionDerivation
import QEDFV.HOL.TypeDefExamples
import QEDFV.HOL.Concrete

/-! A worked example of the typedef derivation constructor: the one-element subtype
`{x : bool // x = True}` of `bool`, introduced at a history by a hypothesis-free witness
derivation `⊢ P True`, with the three laws derived as conclusions at the extended history,
an old-language theorem lifted across the step with `weaken`, and non-triviality of the
extended model. -/
namespace QEDFV.HOL

/-- Non-triviality along a history with type definitions: the generic false sentence is not
valid at any history's model pair. (The model pair is admissible by construction.) -/
theorem typed_signature_generic_nonvalid_in_history {S : Signature}
    (es : List (ModelExtension S)) (M : Model S) :
    ¬ Valid (interpretModels es M).I
      { hyps := [], concl := signatureGenericFalseSentence S } :=
  signatureGenericFalseSentence_not_valid S (interpretModels es M).I
    ⟨fun _ ↦ ⟨()⟩, (interpretModels es M).adm⟩

namespace Derivation

variable {S : Signature} {Γ : List Ty}

/-- From `⊢ p = q` and `⊢ q` derive `⊢ p` (symmetry of `=` followed by `eqMp`). -/
theorem of_eq_left {p q : Term S Γ .bool} (hA : Derivation S ⟨[], p.equal q⟩)
    (hB : Derivation S ⟨[], q⟩) : Derivation S ⟨[], p⟩ := by
  have s1 : Derivation S ⟨union [] [], (Term.eq.app p).equal (Term.eq.app q)⟩ :=
    Derivation.mkComb (A := ⟨[], (Term.eq (a := .bool)).equal Term.eq⟩) (B := ⟨[], p.equal q⟩)
      rfl rfl (Derivation.refl _) hA
  have s2 : Derivation S ⟨union (union [] []) [],
      ((Term.eq.app p).app p).equal ((Term.eq.app q).app p)⟩ :=
    Derivation.mkComb (A := ⟨union [] [], (Term.eq.app p).equal (Term.eq.app q)⟩)
      (B := ⟨[], p.equal p⟩) rfl rfl s1 (Derivation.refl p)
  have s3 : Derivation S ⟨union (union (union [] []) []) [], q.equal p⟩ :=
    Derivation.eqMp (A := ⟨union (union [] []) [], _⟩) (B := ⟨[], p.equal p⟩)
      rfl rfl s2 (Derivation.refl p)
  exact Derivation.eqMp (A := ⟨union (union (union [] []) []) [], q.equal p⟩) (B := ⟨[], q⟩)
    rfl rfl s3 hB

end Derivation

/-- Constructor `0` (arity `0`) over `bool` with predicate `λx. x = True`: a one-element
type. Constant `0` is `Rep`, constant `1` is `Abs` (`exSig`). -/
def unitGate : TypeDefGate exSig :=
  exGate (Term.lam ((Term.var Var.zero).equal Term.truth))
    (fun i hi ↦ by simp [Term.annotVars, Ty.typeVars] at hi)
    (by simp [Term.tyCons, Ty.tyCons]) (by simp [Term.constIds]) (by simp [Term.constIds])

/-- The witness derivation `⊢ P True`, in the empty history: `beta`, `refl`, and the
symmetry-and-`eqMp` step `Derivation.of_eq_left`. -/
theorem unitGate_witness_derivation :
    Derivation exSig ⟨[], unitGate.pred.app Term.truth⟩ :=
  Derivation.of_eq_left (Derivation.beta _ Term.truth) (Derivation.refl Term.truth)

/-- The history consisting of the single step `unitGate`. -/
def unitHistory : List (ModelExtension exSig) := [.typeDefinition unitGate]

theorem unitGate_fresh_k : unitGate.k ∉ modelHistoryTyCons ([] : List (ModelExtension exSig)) := by
  simp [modelHistoryTyCons]

theorem unitGate_fresh_rep : unitGate.rep ∉ modelHistoryIds ([] : List (ModelExtension exSig)) := by
  simp [modelHistoryIds]

theorem unitGate_fresh_abs : unitGate.abs ∉ modelHistoryIds ([] : List (ModelExtension exSig)) := by
  simp [modelHistoryIds]

/-- The law derivation of the example, for any selector. -/
theorem unit_law_derivation (l : TypeDefLaw) :
    ExtensionDerivation exSig unitHistory (l.sequent unitGate) :=
  ExtensionDerivation.typedef unitGate l unitGate_fresh_k unitGate_fresh_rep unitGate_fresh_abs
    Term.truth (ExtensionDerivation.core unitGate_witness_derivation)

/-- `⊢ Abs (Rep a) = a` at the extended history. -/
theorem unit_absRep_derivation :
    ExtensionDerivation exSig unitHistory unitGate.absRepSequent :=
  unit_law_derivation .absRep

/-- `⊢ P (Rep a)` at the extended history. -/
theorem unit_repRange_derivation :
    ExtensionDerivation exSig unitHistory unitGate.repRangeSequent :=
  unit_law_derivation .repRange

/-- `P r ⊢ Rep (Abs r) = r` at the extended history. -/
theorem unit_repAbs_derivation :
    ExtensionDerivation exSig unitHistory unitGate.repAbsSequent :=
  unit_law_derivation .repAbs

/-- The model pair of the extended history, over the default base model. -/
noncomputable def unitModel : Model exSig := interpretModels unitHistory (Model.default exSig)

/-- The three derived laws are valid at the extended model pair (soundness). -/
theorem unit_laws_valid :
    Valid unitModel.I unitGate.absRepSequent ∧ Valid unitModel.I unitGate.repRangeSequent ∧
      Valid unitModel.I unitGate.repAbsSequent :=
  ⟨typed_extension_derivation_sound_default unit_absRep_derivation,
   typed_extension_derivation_sound_default unit_repRange_derivation,
   typed_extension_derivation_sound_default unit_repAbs_derivation⟩

/-- A theorem of the old language, derived by the core rules, lifted across the step with
`weaken`: the side condition holds because the sequent mentions neither the constructor `0`
nor the constants `0`, `1`. -/
theorem unit_old_language_derivation :
    ExtensionDerivation exSig unitHistory
      (⟨[], (Term.truth (S := exSig) (Γ := [])).equal Term.truth⟩ : Sequent exSig []) :=
  ExtensionDerivation.weaken (.typeDefinition unitGate)
    (ExtensionDerivation.core (Derivation.refl Term.truth))
    (by simp [ModelExtension.oldLanguage, unitGate, exGate, Sequent.tyCons, Sequent.constIds,
      Term.tyCons, Term.constIds, Ty.tyCons])

/-- Non-triviality at the extended model: `False` is not valid. -/
theorem unit_model_nontrivial :
    ¬ Valid unitModel.I { hyps := [], concl := signatureGenericFalseSentence exSig } :=
  typed_signature_generic_nonvalid_in_history _ _

/-- Derivation-level conservativity for the example: the old-language theorem is valid at
the canonical base model. -/
theorem unit_old_language_valid :
    Valid (canonicalConstVal defaultTyCon exSig)
      (⟨[], (Term.truth (S := exSig) (Γ := [])).equal Term.truth⟩ : Sequent exSig []) :=
  extension_derivation_old_language_valid defaultTyCon_isAdmissible unit_old_language_derivation
    (by
      intro e he
      obtain rfl : e = .typeDefinition unitGate := by simpa [unitHistory] using he
      simp [ModelExtension.oldLanguage, unitGate, exGate, Sequent.tyCons, Sequent.constIds,
        Term.tyCons, Term.constIds, Ty.tyCons])

end QEDFV.HOL
