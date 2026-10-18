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

theorem trans_cast (hC : G.Closed) {Γ : List Ty} {a b : Ty} (h : a = b) (t : Term S Γ a) :
    G.trans hC (h ▸ t) = (congrArg G.tr h) ▸ G.trans hC t := by
  subst h; rfl

theorem repI_app {Γ : List Ty} {es : List (ModelExtension S)} {L : List (Term S Γ .bool)}
    (z : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := L, concl := ((G.repI Γ).app z).equal (G.nrm z) } := by
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta ((Term.lam (Term.var Var.zero)).app (G.nrm (Term.var Var.zero))) z)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have hb : (((Term.lam (Term.var Var.zero)).app (G.nrm (Term.var Var.zero))).substitute
      (Sub.single z) : Term S Γ G.repTy)
      = (Term.lam (Term.var Var.zero)).app (G.nrm z) := by
    simp only [Term.substitute, G.nrm_substitute]; rfl
  rw [hb] at b1
  have b2 := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.var Var.zero : Term S (G.repTy :: Γ) G.repTy) (G.nrm z))).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.trans' b1 b2

theorem absI_app {Γ : List Ty} {es : List (ModelExtension S)} {L : List (Term S Γ .bool)}
    (z : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := L, concl := ((G.absI Γ).app z).equal (G.nrm z) } := by
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta (G.nrm ((Term.lam (Term.var Var.zero)).app (Term.var Var.zero))) z)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have hb : ((G.nrm ((Term.lam (Term.var Var.zero)).app (Term.var Var.zero))).substitute
      (Sub.single z) : Term S Γ G.repTy)
      = G.nrm ((Term.lam (Term.var Var.zero)).app z) := by
    rw [G.nrm_substitute]; rfl
  rw [hb] at b1
  have b2 := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.var Var.zero : Term S (G.repTy :: Γ) G.repTy) z)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have b3 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (L := L) (G.normIn Γ)) b2
  exact HistoryDerivation.trans' b1 b3

end TypeDefGate

theorem Term.instType_cast {S : Signature} {Γ : List Ty} {a b : Ty} (h : a = b) (t : Term S Γ a)
    (θ : TypeSub) : (h ▸ t).instType θ = (congrArg (Ty.subst θ) h) ▸ t.instType θ := by
  subst h; rfl

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

theorem trans_repTerm_heq (hC : G.Closed) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC ((G.repTerm (Γ := Γ)).instType θ)) (G.repI (Γ.map (Ty.subst θ) |>.map G.tr)) := by
  unfold repTerm
  rw [Term.instType_cast]
  simp only [Term.instType]
  rw [G.trans_cast hC, G.trans_cast hC]
  exact (eqRec_heq _ _).trans ((eqRec_heq _ _).trans (G.trans_rep_heq hC _))

theorem trans_absTerm_heq (hC : G.Closed) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC ((G.absTerm (Γ := Γ)).instType θ)) (G.absI (Γ.map (Ty.subst θ) |>.map G.tr)) := by
  unfold absTerm
  rw [Term.instType_cast]
  simp only [Term.instType]
  rw [G.trans_cast hC, G.trans_cast hC]
  exact (eqRec_heq _ _).trans ((eqRec_heq _ _).trans (G.trans_abs_heq hC _))

end TypeDefGate

theorem HistoryDerivation.app_heq {S : Signature} {Γ : List Ty} {es : List (ModelExtension S)}
    {L : List (Term S Γ .bool)} {A B A' B' : Ty} (hA : A = A') (hB : B = B')
    {f : Term S Γ (.arr A B)} {g : Term S Γ (.arr A' B')} (hfg : HEq f g) (y : Term S Γ A) :
    HistoryDerivation S es { hyps := L, concl := (f.app y).equal (hB ▸ g.app (hA ▸ y)) } := by
  subst hA; subst hB
  have := eq_of_heq hfg
  subst this
  exact HistoryDerivation.refl' _

end QEDFV.HOL
