import QEDFV.Signature.TypeGrammar

namespace QEDFV

abbrev TypeSubst := List (TVar × HolType)

def lookupTypeSubst (s : TypeSubst) (v : TVar) : Option HolType :=
  match s.find? (fun p => p.fst = v) with
  | some (_, ty) => some ty
  | none => none

mutual

def applyTypeSubst (s : TypeSubst) : HolType -> HolType
  | .tyvar v =>
      match lookupTypeSubst s v with
      | some ty => ty
      | none => .tyvar v
  | .tyapp k args => .tyapp k (applyTypeSubstList s args)

def applyTypeSubstList (s : TypeSubst) : List HolType -> List HolType
  | [] => []
  | ty :: rest => applyTypeSubst s ty :: applyTypeSubstList s rest

end

def applyTypeSubstToTermTyvars (s : TypeSubst) (ty : HolType) : List TVar :=
  tyvars (applyTypeSubst s ty)

@[simp] theorem lookupTypeSubst_nil (v : TVar) :
    lookupTypeSubst [] v = none := by
  rfl

@[simp] theorem applyTypeSubst_nil_tyvar (v : TVar) :
    applyTypeSubst [] (.tyvar v) = .tyvar v := by
  rfl

end QEDFV
