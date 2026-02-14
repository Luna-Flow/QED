import QEDFV.Signature.ScopedStack
import QEDFV.Signature.ConstSchemes

namespace QEDFV

inductive RTerm where
  | rVar : String -> HolType -> RTerm
  | rConst : ConstName -> HolType -> RTerm
  | rComb : RTerm -> RTerm -> RTerm
  | rAbs : String -> HolType -> RTerm -> RTerm
deriving Repr, BEq

inductive Elaborates : ScopeStack -> Term -> RTerm -> Prop where
  | var (s n ty) : Elaborates s (.var n ty) (.rVar n ty)
  | const {s n ty}
      (hlookup : lookup s n = some ty) : Elaborates s (.const n ty) (.rConst n ty)
  | comb {s f x rf rx}
      (hf : Elaborates s f rf)
      (hx : Elaborates s x rx) : Elaborates s (.comb f x) (.rComb rf rx)
  | abs {s n ty b rb}
      (hb : Elaborates s b rb) : Elaborates s (.abs n ty b) (.rAbs n ty rb)

inductive ElaboratesWithInstances (env : ConstSchemeEnv) : ScopeStack -> Term -> RTerm -> Prop where
  | var (s n ty) :
      ElaboratesWithInstances env s (.var n ty) (.rVar n ty)
  | const {s n ty}
      (hlookup : lookup s n = some ty)
      (hInst : admissibleConstInstance env n ty) :
      ElaboratesWithInstances env s (.const n ty) (.rConst n ty)
  | comb {s f x rf rx}
      (hf : ElaboratesWithInstances env s f rf)
      (hx : ElaboratesWithInstances env s x rx) :
      ElaboratesWithInstances env s (.comb f x) (.rComb rf rx)
  | abs {s n ty b rb}
      (hb : ElaboratesWithInstances env s b rb) :
      ElaboratesWithInstances env s (.abs n ty b) (.rAbs n ty rb)

theorem elaborates_const_instance
    (env : ConstSchemeEnv)
    (s : ScopeStack)
    (n : ConstName)
    (ty tyGen : HolType)
    (hLookupScope : lookup s n = some ty)
    (hLookupScheme : lookupConstScheme env n = some tyGen)
    (hInst : TyInstance ty tyGen) :
    ElaboratesWithInstances env s (.const n ty) (.rConst n ty) := by
  exact ElaboratesWithInstances.const hLookupScope
    (const_instance_from_principal env n tyGen ty hLookupScheme hInst)

end QEDFV
