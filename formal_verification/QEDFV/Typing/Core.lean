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

inductive CoreTypingWithInstances (env : ConstSchemeEnv) :
    List (String × HolType) -> RTerm -> HolType -> Prop where
  | var {ctx n ty} :
      (n, ty) ∈ ctx ->
      CoreTypingWithInstances env ctx (.rVar n ty) ty
  | const {ctx kappa ty tyGen} :
      lookupConstScheme env kappa = some tyGen ->
      TyInstance ty tyGen ->
      CoreTypingWithInstances env ctx (.rConst kappa ty) ty
  | comb {ctx f x a b}
      (hf : CoreTypingWithInstances env ctx f (funTy a b))
      (hx : CoreTypingWithInstances env ctx x a) :
      CoreTypingWithInstances env ctx (.rComb f x) b
  | abs {ctx n a body b}
      (hb : CoreTypingWithInstances env ((n, a) :: ctx) body b) :
      CoreTypingWithInstances env ctx (.rAbs n a body) (funTy a b)

theorem polymorphic_const_instantiation_admissible
    (env : ConstSchemeEnv)
    (ctx : List (String × HolType))
    (kappa : ConstName)
    (tyGen ty : HolType)
    (hLookup : lookupConstScheme env kappa = some tyGen)
    (hInst : TyInstance ty tyGen) :
    CoreTypingWithInstances env ctx (.rConst kappa ty) ty := by
  exact CoreTypingWithInstances.const hLookup hInst

theorem no_monomorphic_lockout_core
    (env : ConstSchemeEnv)
    (ctx : List (String × HolType))
    (kappa : ConstName)
    (tyGen ty1 ty2 : HolType)
    (hLookup : lookupConstScheme env kappa = some tyGen)
    (h1 : TyInstance ty1 tyGen)
    (h2 : TyInstance ty2 tyGen) :
    CoreTypingWithInstances env ctx (.rConst kappa ty1) ty1 ∧
    CoreTypingWithInstances env ctx (.rConst kappa ty2) ty2 := by
  exact ⟨
    polymorphic_const_instantiation_admissible env ctx kappa tyGen ty1 hLookup h1,
    polymorphic_const_instantiation_admissible env ctx kappa tyGen ty2 hLookup h2
  ⟩

end QEDFV
