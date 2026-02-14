import Lean

namespace QEDFV

abbrev DbExpr := Lean.Expr

def QEDExprWF : DbExpr -> Prop
  | .bvar _ => True
  | .const _ _ => True
  | .app f a => QEDExprWF f ∧ QEDExprWF a
  | .lam _ ty body _ => QEDExprWF ty ∧ QEDExprWF body
  | _ => False

def isTypedAbs (e : DbExpr) : Prop :=
  match e with
  | .lam _ ty body _ => QEDExprWF ty ∧ QEDExprWF body
  | _ => False

theorem typed_core_injectivity
    (n1 n2 : Lean.Name) (ty1 ty2 body1 body2 : DbExpr)
    (bi1 bi2 : Lean.BinderInfo)
    (h : Lean.Expr.lam n1 ty1 body1 bi1 = Lean.Expr.lam n2 ty2 body2 bi2) :
    ty1 = ty2 ∧ body1 = body2 := by
  cases h
  simp

end QEDFV
