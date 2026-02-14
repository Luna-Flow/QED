import QEDFV.Db.ExprCore

namespace QEDFV

abbrev dbHasLooseBVar (e : DbExpr) (i : Nat) : Bool := e.hasLooseBVar i
abbrev dbLiftLooseBVars (e : DbExpr) (cutoff delta : Nat) : DbExpr := e.liftLooseBVars cutoff delta
abbrev dbLowerLooseBVars (e : DbExpr) (cutoff delta : Nat) : DbExpr := e.lowerLooseBVars cutoff delta
abbrev dbInstantiate (e : DbExpr) (subst : Array DbExpr) : DbExpr := e.instantiate subst
abbrev dbInstantiate1 (e arg : DbExpr) : DbExpr := e.instantiate1 arg
abbrev dbInstantiateRev (e : DbExpr) (subst : Array DbExpr) : DbExpr := e.instantiateRev subst
abbrev dbAbstract (e : DbExpr) (xs : Array DbExpr) : DbExpr := e.abstract xs

def paperShift (delta cutoff : Nat) (d : DbExpr) : DbExpr :=
  dbLiftLooseBVars d cutoff delta

def paperLower (delta cutoff : Nat) (d : DbExpr) : DbExpr :=
  dbLowerLooseBVars d cutoff delta

def paperSubst1 (body arg : DbExpr) : DbExpr :=
  dbInstantiate1 body arg

theorem paper_shift_uses_lean_api (delta cutoff : Nat) (d : DbExpr) :
    paperShift delta cutoff d = d.liftLooseBVars cutoff delta := by
  rfl

theorem paper_subst1_uses_lean_api (body arg : DbExpr) :
    paperSubst1 body arg = body.instantiate1 arg := by
  rfl

end QEDFV
