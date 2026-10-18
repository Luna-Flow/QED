import QEDFV.HOL.TdNorm

/-! The translation of terms for the erasure of a type definition with closed representation
type. Variables stay variables (their context hypotheses say they are normalised), binders
substitute the normalised variable, and constants are normalised at their type. -/
namespace QEDFV.HOL

/-- The variable map of the type translation. -/
def Var.mapTy (f : Ty → Ty) : {Γ : List Ty} → {a : Ty} → Var Γ a → Var (Γ.map f) (f a)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (Var.mapTy f v)

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- The type translation of the gate. -/
abbrev tr (a : Ty) : Ty := a.tr G.k G.n G.repTy

theorem tr_con_pos {j m : Nat} {args : Fin m → Ty} (h : j = G.k ∧ m = G.n) :
    G.tr (.con j m args) = G.repTy := by
  simp [tr, Ty.tr, h]

theorem tr_con_neg {j m : Nat} {args : Fin m → Ty} (h : ¬ (j = G.k ∧ m = G.n)) :
    G.tr (.con j m args) = .con j m (fun i ↦ G.tr (args i)) := by
  simp [tr, Ty.tr, h]

variable {Γ Δ : List Ty}

open Classical in
/-- Normalisation of a term at a type: the identity except at the defined type, where it is
the retraction, and at function types, where it is applied to arguments and results. -/
noncomputable def nrmTy (τ : Ty) {Γ : List Ty} (u : Term S Γ (G.tr τ)) : Term S Γ (G.tr τ) :=
  match τ, Γ, u with
  | .bool, _, u => u
  | .ind, _, u => u
  | .var _, _, u => u
  | .arr a b, _, u =>
      if G.k ∈ (Ty.arr a b).tyCons then
        Term.lam (nrmTy b ((u.rename Var.succ).app (nrmTy a (Term.var Var.zero))))
      else u
  | .con j m _, _, u =>
      if h : j = G.k ∧ m = G.n then
        (G.tr_con_pos h).symm ▸ G.nrm ((G.tr_con_pos h) ▸ u)
      else u

/-- The representation type is closed and free of the defined constructor. -/
def Closed : Prop := ∀ i, i ∉ G.repTy.typeVars

theorem Closed.of_n_zero (hn : G.n = 0) : G.Closed := fun i hi ↦ by
  have := G.repTy_typeVars_lt i hi
  omega

theorem tr_repTy : G.tr G.repTy = G.repTy :=
  Ty.tr_of_not_mem G.repTy (fun h ↦ G.repTy_tyCons_ne G.k h rfl)

open Classical in
/-- The instance substitution of a translated constant: translated on the type variables of the
schema and the identity elsewhere, so that instances agreeing on the schema translate alike. -/
noncomputable def canonSub (c : Nat) (σ : TypeSub) : TypeSub :=
  fun i ↦ if i ∈ (S c).typeVars then G.tr (σ i) else Ty.var i

theorem tr_const_ty (hC : G.Closed) {c : Nat} (h : G.k ∉ (S c).tyCons) (σ : TypeSub) :
    (S c).subst (G.canonSub c σ) = G.tr ((S c).subst σ) := by
  rw [tr, Ty.tr_subst hC, Ty.tr_of_not_mem _ h]
  exact Ty.subst_congr _ (fun i hi ↦ by simp [canonSub, hi, tr])

theorem tr_paramTy_subst (σ : TypeSub) :
    (Ty.subst σ (paramTy G.k G.n)).tr G.k G.n G.repTy = G.repTy := by
  simp [paramTy, Ty.subst, Ty.tr]

theorem tr_repTy_subst (hC : G.Closed) (σ : TypeSub) :
    (Ty.subst σ G.repTy).tr G.k G.n G.repTy = G.repTy := by
  rw [Ty.tr_subst hC]
  have := G.tr_repTy
  simp only [tr] at this
  rw [this]
  exact Ty.subst_of_closed _ hC _

theorem tr_rep_ty (hC : G.Closed) {c : Nat} (h : c = G.rep) (σ : TypeSub) :
    G.tr ((S c).subst σ) = .arr G.repTy G.repTy := by
  subst h
  rw [G.rep_ty]
  simp only [Ty.subst, tr, Ty.tr, G.tr_paramTy_subst σ, G.tr_repTy_subst hC σ]

theorem tr_abs_ty (hC : G.Closed) {c : Nat} (h : c = G.abs) (σ : TypeSub) :
    G.tr ((S c).subst σ) = .arr G.repTy G.repTy := by
  subst h
  rw [G.abs_ty]
  simp only [Ty.subst, tr, Ty.tr, G.tr_paramTy_subst σ, G.tr_repTy_subst hC σ]

open Classical in
/-- The untranslated image of a constant at an instance: the constant itself at the
translated instance when its schema avoids `k`; the identity for `rep` and `abs`; a default
element otherwise. -/
noncomputable def rawConst (hC : G.Closed) (c : Nat) (σ : TypeSub) {Δ : List Ty} :
    Term S Δ (G.tr ((S c).subst σ)) :=
  if h : G.k ∉ (S c).tyCons then
    (G.tr_const_ty hC h σ) ▸ Term.const c (G.canonSub c σ)
  else if h : c = G.rep then
    (G.tr_rep_ty hC h σ).symm ▸ Term.lam (Term.var Var.zero)
  else if h : c = G.abs then
    (G.tr_abs_ty hC h σ).symm ▸ Term.lam (Term.var Var.zero)
  else Term.choice.app (Term.lam Term.truth)

/-- The binder substitution: the bound variable is replaced by its normalisation. -/
noncomputable def nrmSub (a : Ty) (Γ : List Ty) : Sub S (G.tr a :: Γ) (G.tr a :: Γ) :=
  fun {_} v ↦ match v with
    | .zero => G.nrmTy a (Term.var Var.zero)
    | .succ w => Term.var (Var.succ w)

/-- The translation of terms. -/
noncomputable def trans (hC : G.Closed) {Γ : List Ty} {a : Ty} (t : Term S Γ a) :
    Term S (Γ.map G.tr) (G.tr a) :=
  match t with
  | .var v => .var (Var.mapTy G.tr v)
  | .const c σ => G.nrmTy _ (G.rawConst hC c σ)
  | .app f x => .app (trans hC f) (trans hC x)
  | .lam b => .lam ((trans hC b).substitute (G.nrmSub _ _))
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (trans hC p) (trans hC q)
  | .imp p q => .imp (trans hC p) (trans hC q)
  | .all p => .all ((trans hC p).substitute (G.nrmSub _ _))
  | .ex p => .ex ((trans hC p).substitute (G.nrmSub _ _))
  | @Term.eq _ _ a => G.nrmTy (.arr a (.arr a .bool)) (Term.eq)
  | @Term.choice _ _ a => G.nrmTy (.arr (.arr a .bool) a) (Term.choice)

end TypeDefGate

end QEDFV.HOL
