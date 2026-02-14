import QEDFV.Typing.Elaboration

namespace QEDFV

inductive CoreTyping : List (String × HolType) -> RTerm -> HolType -> Prop where
  | var {ctx n ty} : (n, ty) ∈ ctx -> CoreTyping ctx (.rVar n ty) ty
  | const {ctx n ty} : CoreTyping ctx (.rConst n ty) ty
  | comb {ctx f x a b}
      (hf : CoreTyping ctx f (funTy a b))
      (hx : CoreTyping ctx x a) : CoreTyping ctx (.rComb f x) b
  | abs {ctx n a body b}
      (hb : CoreTyping ((n, a) :: ctx) body b) :
      CoreTyping ctx (.rAbs n a body) (funTy a b)

partial def rTypeOf? : List (String × HolType) -> RTerm -> Option HolType
  | ctx, .rVar n ty => if ctx.contains (n, ty) then some ty else none
  | _, .rConst _ ty => some ty
  | ctx, .rComb f x =>
      match rTypeOf? ctx f, rTypeOf? ctx x with
      | some (.tyapp "fun" [a, b]), some tx => if tx == a then some b else none
      | _, _ => none
  | ctx, .rAbs n a body =>
      match rTypeOf? ((n, a) :: ctx) body with
      | some b => some (funTy a b)
      | none => none

end QEDFV
