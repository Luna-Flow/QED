import QEDFV.HOL.Instantiation

namespace QEDFV.HOL

variable {κ : TyConVal}

def indInjectiveBody (S : Signature) :
    Term S [Ty.arr .ind .ind] .bool :=
  .all (.all (
    let f : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] (.arr .ind .ind) :=
      .var (.succ (.succ .zero))
    let x : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] .ind := .var (.succ .zero)
    let y : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] .ind := .var .zero
    .imp ((f.app x).equal (f.app y)) (x.equal y)))

def indNonSurjectiveBody (S : Signature) :
    Term S [Ty.arr .ind .ind] .bool :=
  .ex (.all (
    let f : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] (.arr .ind .ind) :=
      .var (.succ (.succ .zero))
    let x : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] .ind := .var .zero
    let y : Term S [Ty.ind, Ty.ind, Ty.arr .ind .ind] .ind := .var (.succ .zero)
    .imp ((f.app x).equal y) .falsity))

def indInfinitySentence (S : Signature) : Term S [] .bool :=
  .ex (.conj (indInjectiveBody S) (indNonSurjectiveBody S))

theorem indInfinitySentence_valid (S : Signature) (I : ConstVal κ S) :
    Valid I { hyps := [], concl := indInfinitySentence S } := by
  intro ρ hρ η _
  simp only [indInfinitySentence, indInjectiveBody, indNonSurjectiveBody,
    Term.eval_ex, Term.eval_conj, Term.eval_all, Term.eval_imp,
    Term.eval_falsity, Term.eval_equal]
  change ∃ f : Nat → Nat,
    (∀ x y, f x = f y → x = y) ∧ ∃ y, ∀ x, f x = y → False
  refine ⟨Nat.succ, ?_⟩
  constructor
  · intro x y hxy
    exact Nat.succ.inj hxy
  · refine ⟨0, ?_⟩
    intro x hx
    exact Nat.noConfusion hx

end QEDFV.HOL
