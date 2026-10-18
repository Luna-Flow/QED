import QEDFV.HOL.TdLaws

/-! The fixed-point property of translated terms: under the hypotheses that the context
variables are normalised, the translation of a term is its own normalisation. -/
namespace QEDFV.HOL

namespace HistoryDerivation

variable {S : Signature} {Γ : List Ty} {es : List (ModelExtension S)}

/-- Hypotheses that are themselves derivable can be discharged. -/
theorem cutAll {H L : List (Term S Γ .bool)} {c : Term S Γ .bool}
    (hH : ∀ h, h ∈ H → HistoryDerivation S es { hyps := L, concl := h })
    (d : HistoryDerivation S es { hyps := H, concl := c }) :
    HistoryDerivation S es { hyps := L, concl := c } := by
  induction H generalizing L c with
  | nil => exact d.mono (fun _ hh ↦ by simp at hh)
  | cons h H ih =>
      have d' : HistoryDerivation S es { hyps := H, concl := Term.imp h c } := impI d
      exact mp (ih (fun h' hh' ↦ hH h' (List.mem_cons_of_mem _ hh')) d')
        (hH h (List.mem_cons_self ..))

end HistoryDerivation

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {es : List (ModelExtension S)}

/-- The hypotheses that every context variable is normalised. -/
noncomputable def ctxFix : (Γ : List Ty) → List (Term S (Γ.map G.tr) .bool)
  | [] => []
  | a :: Γ => ((G.nrmTy a (Term.var Var.zero)).equal (Term.var Var.zero)) ::
      (ctxFix Γ).map (fun h ↦ h.rename Var.succ)

theorem mem_ctxFix {Γ : List Ty} {a : Ty} (v : Var Γ a) :
    ((G.nrmTy a (Term.var (Var.mapTy G.tr v))).equal (Term.var (Var.mapTy G.tr v)))
      ∈ G.ctxFix Γ := by
  induction v with
  | zero => exact List.mem_cons_self ..
  | succ v ih =>
      refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, ih, ?_⟩)
      simp only [Term.rename, G.nrmTy_rename]
      rfl

theorem ctxFix_tail_subst {Γ : List Ty} (a : Ty) (h : Term S (Γ.map G.tr) .bool) :
    (h.rename Var.succ : Term S (G.tr a :: Γ.map G.tr) .bool).substitute (G.nrmSub a (Γ.map G.tr))
      = h.rename Var.succ := by
  rw [Term.substitute_rename]
  have : @Eq (Sub S (Γ.map G.tr) (G.tr a :: Γ.map G.tr))
      (fun v ↦ G.nrmSub a (Γ.map G.tr) (Var.succ v)) (fun v ↦ Term.var (Var.succ v)) := rfl
  rw [this]
  exact Term.substitute_var h Var.succ

/-- The binder substitution with the bound variable replaced by the normalisation of `e`. -/
noncomputable def nrmSubAt (a : Ty) (Γ' : List Ty) (e : Term S (G.tr a :: Γ') (G.tr a)) :
    Sub S (G.tr a :: Γ') (G.tr a :: Γ') :=
  fun {_} v ↦ match v with
    | .zero => G.nrmTy a e
    | .succ w => Term.var (Var.succ w)

theorem nrmSub_eq_at (a : Ty) (Γ' : List Ty) :
    @Eq (Sub S (G.tr a :: Γ') (G.tr a :: Γ')) (G.nrmSub a Γ')
      (G.nrmSubAt a Γ' (Term.var Var.zero)) := rfl

/-- Substituting a variable by an equal term in the body of a translated abstraction. -/
theorem body_subst_eq {Γ' : List Ty} {a c : Ty} (T : Term S (G.tr a :: Γ') c)
    (e : Term S (G.tr a :: Γ') (G.tr a)) :
    (((T.substitute (G.nrmSub a Γ')).rename (Ren.lift Var.succ)).substitute
      (Sub.single e)) = T.substitute (G.nrmSubAt a Γ' e) := by
  rw [Term.rename_substitute, Term.substitute_substitute]
  congr 1
  funext c' v
  cases v with
  | zero =>
      change ((G.nrmTy a (Term.var Var.zero)).rename (Ren.lift Var.succ)).substitute
        (Sub.single e) = G.nrmTy a e
      rw [G.nrmTy_rename, G.nrmTy_substitute]
      rfl
  | succ w => rfl

theorem subst_nrmSubAt {Γ' : List Ty} {a c : Ty} (T : Term S (G.tr a :: Γ') c)
    (e : Term S (G.tr a :: Γ') (G.tr a)) :
    T.substitute (G.nrmSubAt a Γ' e)
      = (T.rename (Ren.lift Var.succ)).substitute (Sub.single (G.nrmTy a e)) := by
  rw [Term.substitute_rename]
  congr 1
  funext c' v
  cases v <;> rfl

/-- Translated terms are fixed points of normalisation, under the context hypotheses. -/
theorem trans_fixed (hC : G.Closed) {w : Term S [] G.repTy}
    (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) {Γ : List Ty} {a : Ty}
    (t : Term S Γ a) :
    HistoryDerivation S es
      { hyps := G.ctxFix Γ, concl := (G.nrmTy a (G.trans hC t)).equal (G.trans hC t) } := by
  induction t with
  | var v =>
      exact HistoryDerivation.assume' _ (G.mem_ctxFix v)
  | const c σ => exact G.nrmTy_idem hw _ _ _
  | @app Γ a b f x ihf ihx =>
      simp only [trans]
      have h1 := HistoryDerivation.mkComb' ihf (HistoryDerivation.refl' (L := G.ctxFix Γ) (G.trans hC x))
      have h2 := G.nrm_app a b (L := G.ctxFix Γ) (G.trans hC f) (G.trans hC x) (es := es)
      have h3 := G.nrmTy_congr b (HistoryDerivation.mkComb'
        (HistoryDerivation.refl' (L := G.ctxFix Γ) (G.trans hC f)) ihx)
      exact HistoryDerivation.trans' (HistoryDerivation.sym h3)
        (HistoryDerivation.trans' (HistoryDerivation.sym h2) h1)
  | @lam a Γ b b0 ih =>
      by_cases hk : G.k ∈ (Ty.arr a b).tyCons
      swap
      · simp only [trans]
        rw [G.nrmTy_of_not_mem (.arr a b) hk]
        exact HistoryDerivation.refl' _
      simp only [trans]
      rw [G.nrmTy_arr_pos hk]
      refine HistoryDerivation.abs (A := { hyps := G.ctxFix Γ, concl := Term.truth }) ?_
      set Tb := G.trans hC b0 with hTb
      set B := Tb.substitute (G.nrmSub a (Γ.map G.tr)) with hB
      set L' := (weakenSequent (b := G.tr a) ({ hyps := G.ctxFix Γ, concl := Term.truth } :
        Sequent S (Γ.map G.tr))).hyps with hL'
      set x : Term S (G.tr a :: Γ.map G.tr) (G.tr a) := Term.var Var.zero with hx
      have s1 := (HistoryDerivation.core (es := es)
        (Derivation.beta (B.rename (Ren.lift Var.succ)) (G.nrmTy a x))).mono (L := L')
          (fun _ hh ↦ by simp at hh)
      rw [hB, G.body_subst_eq, G.subst_nrmSubAt] at s1
      have s2 := G.nrmTy_congr b s1
      have idem := G.nrmTy_idem hw a L' x
      have s3 := HistoryDerivation.leibniz (p := Tb.rename (Ren.lift Var.succ)) idem
      have s3' := G.nrmTy_congr b s3
      have hBeq : B = (Tb.rename (Ren.lift Var.succ)).substitute (Sub.single (G.nrmTy a x)) := by
        rw [hB, G.nrmSub_eq_at, G.subst_nrmSubAt]
      -- the induction hypothesis, with the bound variable replaced by its normalisation
      have inst := HistoryDerivation.instTerm (es := es) (G.nrmSub a (Γ.map G.tr)) ih
      have hH : ∀ h, h ∈ (G.ctxFix (a :: Γ)).map
          (fun h0 ↦ h0.substitute (G.nrmSub a (Γ.map G.tr))) →
          HistoryDerivation S es { hyps := L', concl := h } := by
        intro h hh
        obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
        rcases List.mem_cons.mp hh0 with rfl | ht
        · simp only [Term.substitute, G.nrmTy_substitute]
          exact G.nrmTy_idem hw a L' x
        · obtain ⟨t, ht', rfl⟩ := List.mem_map.mp ht
          rw [G.ctxFix_tail_subst a t]
          exact HistoryDerivation.assume' _ (List.mem_map.mpr ⟨t, ht', rfl⟩)
      have s4 : HistoryDerivation S es { hyps := L', concl := (G.nrmTy b B).equal B } := by
        refine HistoryDerivation.cutAll hH ?_
        simp only [termSubstSequent, Term.substitute, G.nrmTy_substitute] at inst
        exact inst
      rw [← hBeq] at s3 s3'
      exact HistoryDerivation.trans' s2 (HistoryDerivation.trans' s3' s4)
  | truth => exact HistoryDerivation.refl' _
  | falsity => exact HistoryDerivation.refl' _
  | conj p q _ _ => exact HistoryDerivation.refl' _
  | imp p q _ _ => exact HistoryDerivation.refl' _
  | all p _ => exact HistoryDerivation.refl' _
  | ex p _ => exact HistoryDerivation.refl' _
  | eq => exact G.nrmTy_idem hw _ _ _
  | choice => exact G.nrmTy_idem hw _ _ _

end TypeDefGate

end QEDFV.HOL
