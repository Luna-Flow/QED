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

theorem trans_rep_heq' (hC : G.Closed) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.rep ((S G.rep).subst σ) ⟨σ, rfl⟩))
      (G.repI (Γ.map G.tr)) := by
  refine Term.erase_inj_heq' _ _ rfl (G.tr_rep_ty hC rfl σ) ?_
  have hk : G.k ∈ (Ty.arr (.con G.k G.n (fun i : Fin G.n ↦ (Ty.var i.val).subst σ))
      (G.repTy.subst σ)).tyCons := by simp [Ty.tyCons]
  simp only [trans]
  rw [G.erase_nrmTy_arr (G.S_rep_subst σ) hk]
  have hR : G.k ∉ (G.repTy.subst σ).tyCons := by
    rw [Ty.subst_of_closed _ hC]; exact fun h ↦ G.repTy_tyCons_ne G.k h rfl
  have hS : ¬ G.k ∉ (S G.rep).tyCons := by
    rw [G.rep_ty]; simp [paramTy, Ty.tyCons]
  have hraw : (G.rawConst hC G.rep _ ⟨σ, rfl⟩ : Term S (Γ.map G.tr) _)
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

theorem trans_abs_heq' (hC : G.Closed) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.abs ((S G.abs).subst σ) ⟨σ, rfl⟩))
      (G.absI (Γ.map G.tr)) := by
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
  have hraw : (G.rawConst hC G.abs _ ⟨σ, rfl⟩ : Term S (Γ.map G.tr) _)
      = (G.tr_abs_ty hC rfl σ).symm ▸ (Term.lam (Term.var Var.zero) : Term S (Γ.map G.tr) (.arr G.repTy G.repTy)) := by
    unfold rawConst; rw [dif_neg hS, dif_neg hne, dif_pos rfl]
  have eN := G.tr_repTy_subst hC σ
  rw [G.nrmTy_of_not_mem _ hR, hraw]
  simp only [nrmTy, and_self, dite_true, Term.rename_cast, Term.erase_cast, Term.erase, absI, tr,
    eN, nrm, Term.rename]
  rw [eN]
  rfl

theorem trans_rep_heq (hC : G.Closed) (τ : Ty) (h : (S G.rep).IsInst τ) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.rep τ h)) (G.repI (Γ.map G.tr)) := by
  obtain ⟨σ, rfl⟩ := h
  exact G.trans_rep_heq' hC σ

theorem trans_abs_heq (hC : G.Closed) (τ : Ty) (h : (S G.abs).IsInst τ) {Γ : List Ty} :
    HEq (G.trans hC (Term.const (S := S) (Γ := Γ) G.abs τ h)) (G.absI (Γ.map G.tr)) := by
  obtain ⟨σ, rfl⟩ := h
  exact G.trans_abs_heq' hC σ

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

/-- The standing hypothesis on a gate for the erasure: the representation type and the
predicate do not depend on the type parameters (the parameters may occur only in the new
type). A gate without parameters satisfies it (`Ok.of_n_zero`). -/
structure Ok : Prop where
  closed : G.Closed
  pred_ground : G.pred.annotVars = ∅

theorem Ok.of_n_zero (hn : G.n = 0) : G.Ok where
  closed := Closed.of_n_zero G hn
  pred_ground := by
    ext i; constructor
    · intro hi
      have := G.closed i hi
      omega
    · intro hi; exact absurd hi (by simp)

theorem Ok.pred_kfree (_h : G.Ok) : G.k ∉ G.pred.tyCons := G.k_fresh

theorem heq_closedLift {S : Signature} {A B : Ty} (hAB : A = B) {u : Term S [] A} {v : Term S [] B}
    (huv : HEq u v) (Γ : List Ty) : HEq (u.closedLift : Term S Γ A) (v.closedLift : Term S Γ B) := by
  subst hAB
  have := eq_of_heq huv
  subst this
  rfl

theorem heq_rename_closed {S : Signature} {A B : Ty} (hAB : A = B) {u : Term S [] A}
    {v : Term S [] B} (huv : HEq u v) {Δ : List Ty} (r r' : Ren [] Δ) :
    HEq (u.rename r) (v.rename r') := by
  subst hAB
  have := eq_of_heq huv
  subst this
  rw [Ren.empty_ext r r']

theorem trans_predIn_heq (h : G.Ok) (θ : TypeSub) (Γ : List Ty) :
    HEq (G.trans h.closed ((G.predIn Γ).instType θ))
      (G.predIn ((Γ.map (Ty.subst θ)).map G.tr)) := by
  rw [G.predIn_eq, G.predIn_eq]
  unfold Term.closedLift
  rw [Term.rename_instType, ← G.trans_rename h.closed]
  have hP : HEq (G.trans h.closed (G.pred.instType θ)) G.pred := by
    refine Term.erase_inj_heq' _ _ rfl ?_ ?_
    · have : G.k ∉ (Ty.arr G.repTy Ty.bool).tyCons := by
        simp [Ty.tyCons]; exact fun h' ↦ G.repTy_tyCons_ne G.k h' rfl
      have hv : (Ty.arr G.repTy Ty.bool).typeVars = ∅ := by
        have := (G.pred.ty_annotVars_subset)
        rw [h.pred_ground] at this
        ext i; constructor
        · intro hi; exact this hi
        · intro hi; exact absurd hi (by simp)
      exact G.tr_ground h.closed this hv θ
    · exact G.erase_trans_inst h.closed G.pred G.k_fresh h.pred_ground θ
  have hty : G.tr ((Ty.arr G.repTy Ty.bool).subst θ) = Ty.arr G.repTy Ty.bool := by
    have : G.k ∉ (Ty.arr G.repTy Ty.bool).tyCons := by
      simp [Ty.tyCons]; exact fun h' ↦ G.repTy_tyCons_ne G.k h' rfl
    have hv : (Ty.arr G.repTy Ty.bool).typeVars = ∅ := by
      have := (G.pred.ty_annotVars_subset)
      rw [h.pred_ground] at this
      ext i; constructor
      · intro hi; exact this hi
      · intro hi; exact absurd hi (by simp)
    exact G.tr_ground h.closed this hv θ
  exact heq_rename_closed hty hP _ _

section Laws

variable {es : List (ModelExtension S)}

theorem law1_gen {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.repTy) (hY : Y = G.repTy) {f : Term S Γ' (.arr X Y)} {g : Term S Γ' (.arr Y X)}
    (hf : HEq f (G.repI Γ')) (hg : HEq g (G.absI Γ')) (x : Term S Γ' X)
    {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
    (hyp : HistoryDerivation S es
      { hyps := L, concl := (hX.symm ▸ G.nrm (hX ▸ x) : Term S Γ' X).equal x }) :
    HistoryDerivation S es { hyps := L, concl := (g.app (f.app x)).equal x } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  subst hf'; subst hg'
  have s1 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (es := es) (L := L) (G.absI Γ'))
    (G.repI_app (es := es) (L := L) x)
  have s2 := G.absI_app (es := es) (L := L) (G.nrm x)
  have s3 := (G.nrm_idem hwit x).mono (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.trans' s1 (HistoryDerivation.trans' s2 (HistoryDerivation.trans' s3 hyp))

theorem law2_gen {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.repTy) (hY : Y = G.repTy) {f : Term S Γ' (.arr X Y)} {p : Term S Γ' (.arr Y .bool)}
    (hf : HEq f (G.repI Γ')) (hp : HEq p (G.predIn Γ')) (x : Term S Γ' X)
    {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) :
    HistoryDerivation S es { hyps := L, concl := p.app (f.app x) } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hp' := eq_of_heq hp
  subst hf'; subst hp'
  have s1 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (es := es) (L := L) (G.predIn Γ'))
    (G.repI_app (es := es) (L := L) x)
  have s2 := (G.nrm_range hwit x).mono (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.eqMp' (HistoryDerivation.sym s1) s2

theorem law3_gen {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.repTy) (hY : Y = G.repTy) {f : Term S Γ' (.arr X Y)} {g : Term S Γ' (.arr Y X)}
    {p : Term S Γ' (.arr Y .bool)}
    (hf : HEq f (G.repI Γ')) (hg : HEq g (G.absI Γ')) (hp : HEq p (G.predIn Γ')) (x : Term S Γ' Y)
    {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
    (hyp : HistoryDerivation S es { hyps := L, concl := p.app x }) :
    HistoryDerivation S es { hyps := L, concl := (f.app (g.app x)).equal x } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  have hp' := eq_of_heq hp
  subst hf'; subst hg'; subst hp'
  have s1 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (es := es) (L := L) (G.repI Γ'))
    (G.absI_app (es := es) (L := L) x)
  have s2 := G.repI_app (es := es) (L := L) (G.nrm x)
  have s3 := (G.nrm_idem hwit x).mono (L := L) (fun _ hh ↦ by simp at hh)
  have s4 := HistoryDerivation.cut hyp ((G.nrm_fix hwit x).mono (fun h hh ↦ by
    simp only [List.mem_singleton] at hh
    subst hh
    exact List.mem_cons.mpr (Or.inl rfl)))
  exact HistoryDerivation.trans' s1 (HistoryDerivation.trans' s2 (HistoryDerivation.trans' s3 s4))

end Laws

end TypeDefGate

theorem Term.instType_cast {S : Signature} {Γ : List Ty} {a b : Ty} (h : a = b) (t : Term S Γ a)
    (θ : TypeSub) : (h ▸ t).instType θ = (congrArg (Ty.subst θ) h) ▸ t.instType θ := by
  subst h; rfl

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

theorem trans_repTerm_heq (hC : G.Closed) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC ((G.repTerm (Γ := Γ)).instType θ)) (G.repI (Γ.map (Ty.subst θ) |>.map G.tr)) := by
  unfold repTerm
  exact G.trans_rep_heq hC _ _

theorem trans_absTerm_heq (hC : G.Closed) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans hC ((G.absTerm (Γ := Γ)).instType θ)) (G.absI (Γ.map (Ty.subst θ) |>.map G.tr)) := by
  unfold absTerm
  exact G.trans_abs_heq hC _ _

end TypeDefGate

theorem HistoryDerivation.app_heq {S : Signature} {Γ : List Ty} {es : List (ModelExtension S)}
    {L : List (Term S Γ .bool)} {A B A' B' : Ty} (hA : A = A') (hB : B = B')
    {f : Term S Γ (.arr A B)} {g : Term S Γ (.arr A' B')} (hfg : HEq f g) (y : Term S Γ A) :
    HistoryDerivation S es { hyps := L, concl := (f.app y).equal (hB ▸ g.app (hA ▸ y)) } := by
  subst hA; subst hB
  have := eq_of_heq hfg
  subst this
  exact HistoryDerivation.refl' _


namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {es : List (ModelExtension S)}

theorem tr_newTy_subst (hC : G.Closed) (θ : TypeSub) :
    G.tr (G.newTy.subst θ) = G.repTy := by
  simpa [newTy, tr] using G.tr_paramTy_subst θ

theorem nrmTy_newTy_subst (hC : G.Closed) (θ : TypeSub) {Γ : List Ty}
    (u : Term S Γ (G.tr (G.newTy.subst θ))) :
    G.nrmTy (G.newTy.subst θ) u
      = ((G.tr_newTy_subst hC θ).symm ▸ G.nrm ((G.tr_newTy_subst hC θ) ▸ u) :
          Term S Γ (G.tr (G.newTy.subst θ))) := by
  simp only [newTy, paramTy, Ty.subst, nrmTy, and_self, dite_true]

theorem trans_law1 (h : G.Ok) (θ : TypeSub)
    {w : Term S [] G.repTy} (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) :
    HistoryDerivation S es (G.transSeq h.closed (typeSubstSequent θ G.absRepSequent)) := by
  refine G.fromEq h.closed hwit (fun h' hh' ↦ ?_) ?_
  · simp only [transSeq, List.mem_append]; exact Or.inl hh'
  refine G.law1_gen (G.tr_newTy_subst h.closed θ) (G.tr_repTy_subst h.closed θ)
    (G.trans_repTerm_heq h.closed θ) (G.trans_absTerm_heq h.closed θ) _ hwit ?_
  have hmem : (G.nrmTy (Ty.subst θ G.newTy) (Term.var Var.zero)).equal (Term.var Var.zero) ∈
      G.ctxFix [Ty.subst θ G.newTy] := List.mem_cons_self ..
  rw [G.nrmTy_newTy_subst h.closed] at hmem
  exact HistoryDerivation.assume' _ (List.mem_append_left _ hmem)

theorem trans_law2 (h : G.Ok) (θ : TypeSub)
    {w : Term S [] G.repTy} (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) :
    HistoryDerivation S es (G.transSeq h.closed (typeSubstSequent θ G.repRangeSequent)) :=
  G.law2_gen (G.tr_newTy_subst h.closed θ) (G.tr_repTy_subst h.closed θ)
    (G.trans_repTerm_heq h.closed θ) (G.trans_predIn_heq h θ _) _ hwit

theorem trans_law3 (h : G.Ok) (θ : TypeSub)
    {w : Term S [] G.repTy} (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) :
    HistoryDerivation S es (G.transSeq h.closed (typeSubstSequent θ G.repAbsSequent)) := by
  refine G.fromEq h.closed hwit (fun h' hh' ↦ ?_) ?_
  · simp only [transSeq, List.mem_append]; exact Or.inl hh'
  refine G.law3_gen (G.tr_newTy_subst h.closed θ) (G.tr_repTy_subst h.closed θ)
    (G.trans_repTerm_heq h.closed θ) (G.trans_absTerm_heq h.closed θ) (G.trans_predIn_heq h θ _)
    _ hwit ?_
  exact HistoryDerivation.assume' _ (List.mem_append_right _ (List.mem_map.mpr
    ⟨((G.predIn [G.repTy]).app (Term.var Var.zero)).instType θ,
      List.mem_singleton_self _, rfl⟩))

end TypeDefGate

end QEDFV.HOL
