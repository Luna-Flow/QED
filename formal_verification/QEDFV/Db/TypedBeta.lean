import QEDFV.Db.Operations

namespace QEDFV

structure TypedBetaRedex where
  binderTy : DbExpr
  body : DbExpr
  arg : DbExpr
deriving Repr

def typedBetaContract (r : TypedBetaRedex) : DbExpr :=
  let liftedArg := paperShift 1 0 r.arg
  let substituted := paperSubst1 r.body liftedArg
  paperLower 1 0 substituted

def betaBinderAgreement (r : TypedBetaRedex) : Prop :=
  QEDExprWF r.binderTy ∧ QEDExprWF r.body ∧ QEDExprWF r.arg

def appendixE_beta_binder_agreement_obligation : Prop :=
  forall r, betaBinderAgreement r -> QEDExprWF (typedBetaContract r)

end QEDFV
