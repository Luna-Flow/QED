import QEDFV.Signature.ScopedStack

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

end QEDFV
