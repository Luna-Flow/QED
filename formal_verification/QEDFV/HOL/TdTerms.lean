import QEDFV.HOL.TdNorm

/-! The translation of terms for the erasure of a type definition. Variables stay variables
(their context hypotheses say they are normalised), binders substitute the normalised variable,
and constants are normalised at their type. The normaliser at a type with head `k` is an
*oracle*, a family of closed terms, so that the translation is structurally recursive; the
oracle is constructed afterwards (`TdGood`). -/
namespace QEDFV.HOL

/-- The variable map of the type translation. -/
def Var.mapTy (f : Ty → Ty) : {Γ : List Ty} → {a : Ty} → Var Γ a → Var (Γ.map f) (f a)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (Var.mapTy f v)

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- The type translation of the gate. -/
abbrev tr (a : Ty) : Ty := a.tr G.k G.n G.repTy

/-- The translated arguments of an instance of the new type, as a substitution. -/
abbrev trSub (σ : TypeSub) : TypeSub := fun i ↦ G.tr (σ i)

theorem tr_con_pos {j m : Nat} {args : Fin m → Ty} (h : j = G.k ∧ m = G.n) :
    G.tr (.con j m args) = G.repTy.subst (Ty.argsSub m (fun i ↦ G.tr (args i))) := by
  simp [tr, Ty.tr, h]

theorem tr_con_neg {j m : Nat} {args : Fin m → Ty} (h : ¬ (j = G.k ∧ m = G.n)) :
    G.tr (.con j m args) = .con j m (fun i ↦ G.tr (args i)) := by
  simp [tr, Ty.tr, h]

theorem tr_subst (a : Ty) (σ : TypeSub) : G.tr (a.subst σ) = (G.tr a).subst (G.trSub σ) :=
  Ty.tr_subst G.repTy_typeVars_lt a σ

theorem tr_repTy : G.tr G.repTy = G.repTy :=
  Ty.tr_of_not_mem G.repTy (fun h ↦ G.repTy_tyCons_ne G.k h rfl)

/-- The oracle: the normaliser at every type. Only its values at types with head `k` matter. -/
def Oracle : Type := ∀ τ : Ty, Term S [] (.arr (G.tr τ) (G.tr τ))

variable {Γ Δ : List Ty}

open Classical in
/-- Normalisation of a term at a type: the identity except at the defined type, where it is the
oracle, and at function types, where it is applied to arguments and results. -/
noncomputable def nrmTy (N : G.Oracle) (τ : Ty) {Γ : List Ty} (u : Term S Γ (G.tr τ)) :
    Term S Γ (G.tr τ) :=
  match τ, Γ, u with
  | .bool, _, u => u
  | .ind, _, u => u
  | .var _, _, u => u
  | .arr a b, _, u =>
      if G.k ∈ (Ty.arr a b).tyCons then
        Term.lam (nrmTy N b ((u.rename Var.succ).app (nrmTy N a (Term.var Var.zero))))
      else u
  | .con j m args, _, u =>
      if j = G.k ∧ m = G.n then ((N (.con j m args)).closedLift).app u else u

theorem IsInst_tr {c : Nat} (h : G.k ∉ (S c).tyCons) {τ : Ty}
    (hτ : (S c).IsInst τ) : (S c).IsInst (G.tr τ) := by
  obtain ⟨σ, rfl⟩ := hτ
  refine ⟨G.trSub σ, ?_⟩
  rw [G.tr_subst, show G.tr (S c) = S c from Ty.tr_of_not_mem _ h]

/-- The translation of the new type at the instance `σ`: the representation type at the
translated arguments. -/
theorem tr_newTy_subst (σ : TypeSub) :
    G.tr (G.newTy.subst σ) = G.repTy.subst (G.trSub σ) := by
  have : G.newTy.subst σ = .con G.k G.n (fun i : Fin G.n ↦ σ i.val) := rfl
  rw [this, G.tr_con_pos ⟨rfl, rfl⟩]
  refine Ty.subst_congr G.repTy (fun i hi ↦ ?_)
  have hi' : i < G.n := G.repTy_typeVars_lt i hi
  simp [Ty.argsSub, hi', trSub]

theorem tr_repTy_subst (σ : TypeSub) :
    G.tr (G.repTy.subst σ) = G.repTy.subst (G.trSub σ) := by
  rw [G.tr_subst, G.tr_repTy]

theorem tr_rep_ty {c : Nat} (h : c = G.rep) (σ : TypeSub) :
    G.tr ((S c).subst σ) =
      .arr (G.repTy.subst (G.trSub σ)) (G.repTy.subst (G.trSub σ)) := by
  subst h
  rw [G.rep_ty]
  change G.tr (Ty.arr (G.newTy.subst σ) (G.repTy.subst σ)) = _
  simp only [tr, Ty.tr]
  exact congrArg₂ Ty.arr (G.tr_newTy_subst σ) (G.tr_repTy_subst σ)

theorem tr_abs_ty {c : Nat} (h : c = G.abs) (σ : TypeSub) :
    G.tr ((S c).subst σ) =
      .arr (G.repTy.subst (G.trSub σ)) (G.repTy.subst (G.trSub σ)) := by
  subst h
  rw [G.abs_ty]
  change G.tr (Ty.arr (G.repTy.subst σ) (G.newTy.subst σ)) = _
  simp only [tr, Ty.tr]
  exact congrArg₂ Ty.arr (G.tr_repTy_subst σ) (G.tr_newTy_subst σ)

/-- The identity at an arrow type `X → X`, and a default element at every other type. -/
noncomputable def idTerm (T : Ty) (Δ : List Ty) : Term S Δ T :=
  open Classical in
  match T with
  | .arr X Y => if h : X = Y then h ▸ Term.lam (Term.var Var.zero)
      else Term.choice.app (Term.lam Term.truth)
  | _ => Term.choice.app (Term.lam Term.truth)

theorem erase_idTerm {T X : Ty} (h : T = .arr X X) (Δ : List Ty) :
    (idTerm (S := S) T Δ).erase = UTerm.lam X (UTerm.var 0) := by
  subst h
  simp [idTerm, Term.erase, Var.erase]

open Classical in
/-- The untranslated image of a constant at an instance: the constant itself at the
translated instance when its schema avoids `k`; the identity for `rep` and `abs`; a default
element otherwise. -/
noncomputable def rawConst (c : Nat) (τ : Ty) (hτ : (S c).IsInst τ) {Δ : List Ty} :
    Term S Δ (G.tr τ) :=
  if h : G.k ∉ (S c).tyCons then
    Term.const c (G.tr τ) (G.IsInst_tr h hτ)
  else if c = G.rep ∨ c = G.abs then idTerm (S := S) (G.tr τ) Δ
  else Term.choice.app (Term.lam Term.truth)

/-- The binder substitution: the bound variable is replaced by its normalisation. -/
noncomputable def nrmSub (N : G.Oracle) (a : Ty) (Γ : List Ty) :
    Sub S (G.tr a :: Γ) (G.tr a :: Γ) :=
  fun {_} v ↦ match v with
    | .zero => G.nrmTy N a (Term.var Var.zero)
    | .succ w => Term.var (Var.succ w)

/-- The translation of terms. -/
noncomputable def trans (N : G.Oracle) {Γ : List Ty} {a : Ty} (t : Term S Γ a) :
    Term S (Γ.map G.tr) (G.tr a) :=
  match t with
  | .var v => .var (Var.mapTy G.tr v)
  | .const c τ h => G.nrmTy N _ (G.rawConst c τ h)
  | .app f x => .app (trans N f) (trans N x)
  | .lam b => .lam ((trans N b).substitute (G.nrmSub N _ _))
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (trans N p) (trans N q)
  | .imp p q => .imp (trans N p) (trans N q)
  | .all p => .all ((trans N p).substitute (G.nrmSub N _ _))
  | .ex p => .ex ((trans N p).substitute (G.nrmSub N _ _))
  | @Term.eq _ _ a => G.nrmTy N (.arr a (.arr a .bool)) (Term.eq)
  | @Term.choice _ _ a => G.nrmTy N (.arr (.arr a .bool) a) (Term.choice)

end TypeDefGate

end QEDFV.HOL
