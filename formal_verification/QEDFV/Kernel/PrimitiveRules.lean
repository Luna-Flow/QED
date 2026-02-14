import QEDFV.Kernel.ThmObject
import QEDFV.Signature.GlobalLocalState

namespace QEDFV

def mkEqExpr (lhs rhs : DbExpr) : DbExpr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq []) lhs) rhs

def EqExpr (e : DbExpr) : Prop :=
  match e with
  | Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq _) _) _ => True
  | _ => False

def IsBoolExpr (e : DbExpr) : Prop := EqExpr e

theorem isBoolExpr_mkEqExpr (lhs rhs : DbExpr) : IsBoolExpr (mkEqExpr lhs rhs) := by
  simp [IsBoolExpr, EqExpr, mkEqExpr]

inductive Derivable (k : KernelState) : Sequent -> Prop where
  | refl (t : DbExpr) :
      Derivable k { hyps := [], concl := mkEqExpr t t }
  | assume (p : DbExpr) :
      IsBoolExpr p ->
      Derivable k { hyps := [p], concl := p }
  | trans (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := B.concl }
  | mkComb (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := A.concl }
  | abs (A : Sequent) :
      Derivable k A -> Derivable k A
  | beta (A : Sequent) :
      Derivable k A -> Derivable k A
  | eqMp (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := B.concl }
  | deductAntisym (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := A.concl }
  | instType (A : Sequent) :
      Derivable k A -> Derivable k A
  | inst (A : Sequent) :
      Derivable k A -> Derivable k A

end QEDFV
