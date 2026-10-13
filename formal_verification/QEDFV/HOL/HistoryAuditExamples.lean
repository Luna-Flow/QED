import QEDFV.HOL.HistoryDerivation
import QEDFV.HOL.TypeDefDerivationExamples

/-! Negative checks for the fixed-signature history calculus. The empty predicate cannot
supply the witness premise of `HistoryDerivation.typedef`, even after arbitrary model
extensions. The unit example's identifiers are no longer fresh after its first introduction.
These checks concern the constructor premises, not growing-signature admission, persistence
of prior declaration equations, or the executable MoonBit kernel. -/
namespace QEDFV.HOL

/-- The empty predicate has no semantic witness in any admissible model. The admissible
base valuation is exhibited explicitly, so the negation is not vacuous. -/
theorem falseGate_no_witness (M : Model exSig) : ¬ falseGate.WitnessAt M.I := by
  intro h
  obtain ⟨x, hx⟩ := h baseTypeVal ⟨fun _ ↦ ⟨()⟩, M.adm⟩
  exact hx

/-- No closed term can make the required empty-predicate witness sequent valid. -/
theorem falseGate_witness_not_valid (M : Model exSig) (w : Term exSig [] falseGate.repTy) :
    ¬ Valid M.I { hyps := [], concl := falseGate.pred.app w } := by
  intro h
  exact falseGate_no_witness M (falseGate.witnessAt_of_valid M.I w h)

/-- History soundness rules out an empty-predicate witness derivation at every history.
This does not merely inspect the syntactic shape of a proposed witness proof. -/
theorem falseGate_witness_not_derivable (es : List (ModelExtension exSig))
    (w : Term exSig [] falseGate.repTy) :
    ¬ HistoryDerivation exSig es { hyps := [], concl := falseGate.pred.app w } := by
  intro d
  exact falseGate_witness_not_valid (interpretModels es (Model.default exSig)) w
    (typed_history_derivation_sound defaultTyCon_isAdmissible d)

/-- All three identifiers have already been introduced by the one-step unit history. -/
theorem unitGate_ids_in_history :
    unitGate.k ∈ modelHistoryTyCons unitHistory ∧
      unitGate.rep ∈ modelHistoryIds unitHistory ∧
      unitGate.abs ∈ modelHistoryIds unitHistory := by
  simp [modelHistoryTyCons, modelHistoryIds, unitHistory,
    ModelExtension.tyConIds, ModelExtension.constantIds]

/-- Repeating this gate after the unit history cannot satisfy the three freshness premises
of `HistoryDerivation.typedef`. This makes no claim that its law sequents are underivable. -/
theorem unitGate_not_fresh_after_introduction :
    ¬ (unitGate.k ∉ modelHistoryTyCons unitHistory ∧
      unitGate.rep ∉ modelHistoryIds unitHistory ∧
      unitGate.abs ∉ modelHistoryIds unitHistory) := by
  intro h
  exact h.1 unitGate_ids_in_history.1

end QEDFV.HOL
