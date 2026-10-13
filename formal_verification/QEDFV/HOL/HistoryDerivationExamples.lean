import QEDFV.HOL.HistoryDerivation
import QEDFV.HOL.TypeDefDerivationExamples

/-! A non-vacuous composition of a type-definition product with a core inference rule. -/
namespace QEDFV.HOL

/-- A closed equation between the function `Abs ∘ Rep` and the identity of the unit type. -/
def unitAbsRepFunctionSequent : Sequent exSig [] :=
  { hyps := []
  , concl :=
      (Term.lam (unitGate.absTerm.app (unitGate.repTerm.app (Term.var Var.zero)))).equal
        (Term.lam (Term.var Var.zero)) }

/-- Abstraction composes the introduced `Abs (Rep a) = a` law into the closed function
equation `λa. Abs (Rep a) = λa. a` at the one-element type-definition history. -/
theorem unit_absRep_function_derivation :
    HistoryDerivation exSig unitHistory unitAbsRepFunctionSequent := by
  exact HistoryDerivation.abs (A := ⟨[], Term.truth⟩)
    (HistoryDerivation.extension unit_absRep_derivation)

/-- The composed function equation is valid in the existing unit model. -/
theorem unit_absRep_function_valid : Valid unitModel.I unitAbsRepFunctionSequent :=
  typed_history_derivation_sound defaultTyCon_isAdmissible unit_absRep_function_derivation

/-- The example's model has an admissible valuation, is local, validates the composed
equation, and refutes the generic false sentence. The validity claim is therefore non-vacuous. -/
theorem unit_history_composition_nonvacuous :
    Admissible unitModel.κ baseTypeVal ∧ unitModel.IsLocal ∧
      Valid unitModel.I unitAbsRepFunctionSequent ∧
      ¬ Valid unitModel.I { hyps := [], concl := signatureGenericFalseSentence exSig } := by
  refine ⟨⟨fun _ ↦ ⟨()⟩, unitModel.adm⟩, ?_, unit_absRep_function_valid, unit_model_nontrivial⟩
  exact interpretModels_isLocal unitHistory
    (Model.canonical_isLocal defaultTyCon_isAdmissible exSig)

end QEDFV.HOL
