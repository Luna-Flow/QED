import QEDFV.Signature.TypeGrammar

namespace QEDFV

inductive Term where
  | var : String -> HolType -> Term
  | const : String -> HolType -> Term
  | comb : Term -> Term -> Term
  | abs : String -> HolType -> Term -> Term
deriving Repr, BEq

def freeVars : Term -> List (String × HolType)
  | .var n ty => [(n, ty)]
  | .const _ _ => []
  | .comb f x => freeVars f ++ freeVars x
  | .abs n _ body => (freeVars body).filter (fun p => p.fst != n)

def termTyVars : Term -> List TVar
  | .var _ ty => tyvars ty
  | .const _ ty => tyvars ty
  | .comb f x => termTyVars f ++ termTyVars x
  | .abs _ ty body => tyvars ty ++ termTyVars body

def typeOf? : Term -> Option HolType
  | .var _ ty => some ty
  | .const _ ty => some ty
  | .abs _ dom body =>
      match typeOf? body with
      | some cod => some (funTy dom cod)
      | none => none
  | .comb f x =>
      match typeOf? f, typeOf? x with
      | some (.tyapp "fun" [a, b]), some tx => if tx == a then some b else none
      | _, _ => none

def termIsClosed (t : Term) : Prop := freeVars t = []

def termTyvarsSubset (t : Term) (ty : HolType) : Prop :=
  forall v, v ∈ termTyVars t -> v ∈ tyvars ty

end QEDFV
