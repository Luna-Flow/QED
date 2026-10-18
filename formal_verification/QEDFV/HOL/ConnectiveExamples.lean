import QEDFV.HOL.HistoryDerivation

/-! The connective and quantifier rules derive the basic logical facts that the equational
core cannot. -/
namespace QEDFV.HOL

variable {S : Signature}

/-- `⊢ ⊤ ∧ ⊤`. -/
theorem derive_truth_and_truth (es : List (ModelExtension S)) :
    HistoryDerivation S es
      ({ hyps := [], concl := Term.conj Term.truth Term.truth } :
        Sequent S ([] : List Ty)) :=
  HistoryDerivation.conjIntro (A := { hyps := [], concl := Term.truth })
    (B := { hyps := [], concl := Term.truth }) rfl rfl .truthIntro .truthIntro

/-- `⊢ ∀x. x = x`, from reflexivity by generalisation. -/
theorem derive_forall_refl (es : List (ModelExtension S)) (a : Ty) :
    HistoryDerivation S es
      ({ hyps := [], concl := Term.all (a := a) ((Term.var .zero).equal (Term.var .zero)) } :
        Sequent S ([] : List Ty)) :=
  HistoryDerivation.allIntro (A := { hyps := [], concl := Term.truth }) (by
    exact .core (.refl (Term.var .zero)))

/-- `⊢ ⊤ ⟹ ⊤`, by discharging an assumption. -/
theorem derive_imp_self (es : List (ModelExtension S)) :
    HistoryDerivation S es
      ({ hyps := remove [(Term.truth : Term S [] .bool)] Term.truth,
         concl := Term.imp Term.truth Term.truth } : Sequent S ([] : List Ty)) :=
  HistoryDerivation.impIntro (A := { hyps := [Term.truth], concl := Term.truth })
    Term.truth (.core (.assume Term.truth))

end QEDFV.HOL
