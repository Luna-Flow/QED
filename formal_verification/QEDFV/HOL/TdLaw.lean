import QEDFV.HOL.TdKfree

/-! The translation of the type-definition constants `rep` and `abs`. -/
namespace QEDFV.HOL

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- Normalisation at a type equal to an arrow type, computed on the erasure. -/
theorem erase_nrmTy_arr {τ X Y : Ty} (h : τ = .arr X Y) (hk : G.k ∈ (Ty.arr X Y).tyCons)
    {Γ : List Ty} (u : Term S Γ (G.tr τ)) :
    (G.nrmTy τ u).erase
      = (Term.lam (G.nrmTy Y (((congrArg G.tr h ▸ u : Term S Γ (G.tr (.arr X Y))).rename
          Var.succ).app (G.nrmTy X (Term.var Var.zero))))).erase := by
  subst h
  simp only [nrmTy, if_pos hk]

/-- The ideal translation of `rep`: `λx. (λy. y) (norm x)`. -/
noncomputable def repI (Γ : List Ty) : Term S Γ (.arr G.repTy G.repTy) :=
  Term.lam ((Term.lam (Term.var Var.zero)).app (G.nrm (Term.var Var.zero)))

theorem tr_N (σ : TypeSub) :
    G.tr (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ)) = G.repTy :=
  G.tr_con_pos ⟨rfl, rfl⟩

theorem S_rep_subst (σ : TypeSub) :
    (S G.rep).subst σ
      = .arr (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ)) (G.repTy.subst σ) := by
  rw [G.rep_ty]; rfl

theorem trans_rep_heq (hC : G.Closed) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.rep σ)) (G.repI (Γ.map G.tr)) := by
  refine Term.erase_inj_heq' _ _ rfl (G.tr_rep_ty hC rfl σ) ?_
  have hk : G.k ∈ (Ty.arr (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ))
      (G.repTy.subst σ)).tyCons := by simp [Ty.tyCons]
  simp only [trans]
  rw [G.erase_nrmTy_arr (G.S_rep_subst σ) hk]
  have hR : G.k ∉ (G.repTy.subst σ).tyCons := by
    rw [Ty.subst_of_closed _ hC]; exact fun h ↦ G.repTy_tyCons_ne G.k h rfl
  have hS : ¬ G.k ∉ (S G.rep).tyCons := by
    rw [G.rep_ty]; simp [paramTy, Ty.tyCons]
  have hraw : (G.rawConst hC G.rep σ : Term S (Γ.map G.tr) _)
      = (G.tr_rep_ty hC rfl σ).symm ▸ (Term.lam (Term.var Var.zero) : Term S (Γ.map G.tr) (.arr G.repTy G.repTy)) := by
    unfold rawConst; rw [dif_neg hS, dif_pos rfl]
  rw [G.nrmTy_of_not_mem _ hR, hraw]
  have eN := G.tr_N σ
  simp only [tr] at eN
  simp only [nrmTy, and_self, dite_true, Term.rename_cast, Term.erase_cast, Term.erase, repI, tr,
    eN, nrm, Term.rename]
  rw [eN]
  rfl

/-- The ideal translation of `abs`: `λx. norm ((λy. y) x)`. -/
noncomputable def absI (Γ : List Ty) : Term S Γ (.arr G.repTy G.repTy) :=
  Term.lam (G.nrm ((Term.lam (Term.var Var.zero)).app (Term.var Var.zero)))

theorem S_abs_subst (σ : TypeSub) :
    (S G.abs).subst σ
      = .arr (G.repTy.subst σ) (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ)) := by
  rw [G.abs_ty]; rfl

theorem trans_abs_heq (hC : G.Closed) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.abs σ)) (G.absI (Γ.map G.tr)) := by
  refine Term.erase_inj_heq' _ _ rfl (G.tr_abs_ty hC rfl σ) ?_
  have hk : G.k ∈ (Ty.arr (G.repTy.subst σ)
      (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ))).tyCons := by simp [Ty.tyCons]
  simp only [trans]
  rw [G.erase_nrmTy_arr (G.S_abs_subst σ) hk]
  have hR : G.k ∉ (G.repTy.subst σ).tyCons := by
    rw [Ty.subst_of_closed _ hC]; exact fun h ↦ G.repTy_tyCons_ne G.k h rfl
  have hS : ¬ G.k ∉ (S G.abs).tyCons := by
    rw [G.abs_ty]; simp [paramTy, Ty.tyCons]
  have hne : G.abs ≠ G.rep := fun h ↦ G.rep_ne_abs h.symm
  have hraw : (G.rawConst hC G.abs σ : Term S (Γ.map G.tr) _)
      = (G.tr_abs_ty hC rfl σ).symm ▸ (Term.lam (Term.var Var.zero) : Term S (Γ.map G.tr) (.arr G.repTy G.repTy)) := by
    unfold rawConst; rw [dif_neg hS, dif_neg hne, dif_pos rfl]
  have eN := G.tr_repTy_subst hC σ
  rw [G.nrmTy_of_not_mem _ hR, hraw]
  simp only [nrmTy, and_self, dite_true, Term.rename_cast, Term.erase_cast, Term.erase, absI, tr,
    eN, nrm, Term.rename]
  rw [eN]
  rfl

end TypeDefGate

end QEDFV.HOL
