import QEDFV.HOL.TdFL

/-! Translation of sequents and of the rules of the calculus. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QEDFV.HOL

theorem mem_remove_iff {α : Type _} (xs : List α) (x y : α) : y ∈ remove xs x ↔ y ∈ xs ∧ y ≠ x := by
  classical
  simp [remove]

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) (hC : G.Closed) {es : List (ModelExtension S)}

/-- The translation of a sequent: the context hypotheses, then the translated hypotheses. -/
noncomputable def transSeq {Γ : List Ty} (s : Sequent S Γ) : Sequent S (Γ.map G.tr) :=
  { hyps := G.ctxFix Γ ++ s.hyps.map (fun h ↦ (G.trans hC h : Term S (Γ.map G.tr) .bool)),
    concl := (G.trans hC s.concl : Term S (Γ.map G.tr) .bool) }

variable {w : Term S [] G.repTy}

/-- The translation of an equation is the equation of the translations. -/
theorem trans_equal (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
    {Γ : List Ty} {a : Ty} (x y : Term S Γ a) :
    HistoryDerivation S es
      { hyps := G.ctxFix Γ,
        concl := (G.trans hC (x.equal y)).equal ((G.trans hC x).equal (G.trans hC y)) } := by
  simp only [Term.equal, trans]
  have h1 := G.nrm_app a (.arr a .bool) (L := G.ctxFix Γ)
    (Term.eq : Term S _ (G.tr (.arr a (.arr a .bool)))) (G.trans hC x) (es := es)
  have h2 := HistoryDerivation.mkComb' h1
    (HistoryDerivation.refl' (L := G.ctxFix Γ) (G.trans hC y))
  have h3 := G.nrm_app a .bool (L := G.ctxFix Γ)
    ((Term.eq : Term S _ (G.tr (.arr a (.arr a .bool)))).app (G.nrmTy a (G.trans hC x)))
    (G.trans hC y) (es := es)
  have h4 := HistoryDerivation.mkComb'
    (HistoryDerivation.mkComb' (HistoryDerivation.refl' (L := G.ctxFix Γ)
      (Term.eq : Term S _ (G.tr (.arr a (.arr a .bool))))) (G.trans_fixed hC hw x))
    (G.trans_fixed hC hw y)
  exact HistoryDerivation.trans' h2 (HistoryDerivation.trans' h3 h4)

section Steps

variable (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
include hw

theorem mem_ctxFix_append {Γ : List Ty} (hs : List (Term S (Γ.map G.tr) .bool)) :
    ∀ h, h ∈ G.ctxFix Γ → h ∈ G.ctxFix Γ ++ hs := fun h hh ↦ List.mem_append_left _ hh

theorem fromEq {Γ : List Ty} {a : Ty} {x y : Term S Γ a} {L : List (Term S (Γ.map G.tr) .bool)}
    (hL : ∀ h, h ∈ G.ctxFix Γ → h ∈ L)
    (d : HistoryDerivation S es { hyps := L, concl := (G.trans hC x).equal (G.trans hC y) }) :
    HistoryDerivation S es { hyps := L, concl := G.trans hC (x.equal y) } :=
  HistoryDerivation.eqMp' (HistoryDerivation.sym ((G.trans_equal hC hw x y).mono hL)) d

theorem toEq {Γ : List Ty} {a : Ty} {x y : Term S Γ a} {L : List (Term S (Γ.map G.tr) .bool)}
    (hL : ∀ h, h ∈ G.ctxFix Γ → h ∈ L)
    (d : HistoryDerivation S es { hyps := L, concl := G.trans hC (x.equal y) }) :
    HistoryDerivation S es { hyps := L, concl := (G.trans hC x).equal (G.trans hC y) } :=
  HistoryDerivation.eqMp' ((G.trans_equal hC hw x y).mono hL) d

theorem step_refl {Γ : List Ty} {a : Ty} (t : Term S Γ a) :
    HistoryDerivation S es (G.transSeq hC { hyps := [], concl := t.equal t }) := by
  refine G.fromEq hC hw (fun h hh ↦ ?_) (HistoryDerivation.refl' _)
  exact List.mem_append_left _ hh

theorem step_assume {Γ : List Ty} (p : Term S Γ .bool) :
    HistoryDerivation S es (G.transSeq hC { hyps := [p], concl := p }) :=
  HistoryDerivation.assume' _ (by simp [transSeq])

theorem step_addAssum {Γ : List Ty} {A : Sequent S Γ} (p : Term S Γ .bool)
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := p :: A.hyps, concl := A.concl }) :=
  d.mono (fun h hh ↦ by
    simp only [transSeq, List.mem_append, List.mem_map, List.mem_cons] at hh ⊢
    rcases hh with hh | ⟨h0, hh0, rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨h0, Or.inr hh0, rfl⟩)

theorem step_weakenHyps {Γ : List Ty} {A : Sequent S Γ} (L : List (Term S Γ .bool))
    (hL : ∀ h, h ∈ A.hyps → h ∈ L) (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := L, concl := A.concl }) :=
  d.mono (fun h hh ↦ by
    simp only [transSeq, List.mem_append, List.mem_map] at hh ⊢
    rcases hh with hh | ⟨h0, hh0, rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨h0, hL h0 hh0, rfl⟩)

theorem hyps_mono {Γ : List Ty} {A : Sequent S Γ} (L : List (Term S Γ .bool))
    (hL : ∀ h, h ∈ A.hyps → h ∈ L) :
    ∀ h, h ∈ (G.transSeq hC A).hyps → h ∈ (G.transSeq hC { hyps := L, concl := A.concl }).hyps := by
  intro h hh
  simp only [transSeq, List.mem_append, List.mem_map] at hh ⊢
  rcases hh with hh | ⟨h0, hh0, rfl⟩
  · exact Or.inl hh
  · exact Or.inr ⟨h0, hL h0 hh0, rfl⟩

theorem step_trans {Γ : List Ty} {a : Ty} {A B : Sequent S Γ} {x y z : Term S Γ a}
    (hA : A.concl = x.equal y) (hB : B.concl = y.equal z)
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC { hyps := union A.hyps B.hyps, concl := x.equal z }) := by
  cases A with | mk hA' cA => cases B with | mk hB' cB =>
  simp only at hA hB; subst hA; subst hB
  have hL : ∀ h, h ∈ G.ctxFix Γ →
      h ∈ (G.transSeq hC { hyps := union hA' hB', concl := x.equal z }).hyps :=
    fun h hh ↦ by simp [transSeq, hh]
  have eA := G.toEq hC hw hL
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_left _ hh) dA)
  have eB := G.toEq hC hw hL
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_right _ hh) dB)
  exact G.fromEq hC hw hL (HistoryDerivation.trans' eA eB)

theorem step_mkComb {Γ : List Ty} {a b : Ty} {A B : Sequent S Γ} {f g : Term S Γ (.arr a b)}
    {x y : Term S Γ a}
    (hA : A.concl = f.equal g) (hB : B.concl = x.equal y)
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := union A.hyps B.hyps, concl := (f.app x).equal (g.app y) }) := by
  cases A with | mk hA' cA => cases B with | mk hB' cB =>
  simp only at hA hB; subst hA; subst hB
  have hL : ∀ h, h ∈ G.ctxFix Γ →
      h ∈ (G.transSeq hC { hyps := union hA' hB', concl := (f.app x).equal (g.app y) }).hyps :=
    fun h hh ↦ by simp [transSeq, hh]
  have eA := G.toEq hC hw hL
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_left _ hh) dA)
  have eB := G.toEq hC hw hL
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_right _ hh) dB)
  exact G.fromEq hC hw hL (HistoryDerivation.mkComb' eA eB)

theorem step_eqMp {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = p.equal q) (hB : B.concl = p)
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC { hyps := union A.hyps B.hyps, concl := q }) := by
  cases A with | mk hA' cA => cases B with | mk hB' cB =>
  simp only at hA hB; subst hA; subst hB
  have hL : ∀ h, h ∈ G.ctxFix Γ →
      h ∈ (G.transSeq hC { hyps := union hA' hB', concl := q }).hyps :=
    fun h hh ↦ by simp [transSeq, hh]
  have eA := G.toEq hC hw hL
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_left _ hh) dA)
  have eB := G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_right _ hh) dB
  exact HistoryDerivation.eqMp' eA eB

theorem trans_weaken {Γ : List Ty} {a b : Ty} (t : Term S Γ a) :
    (G.trans hC (t.rename Var.succ) : Term S (G.tr b :: Γ.map G.tr) (G.tr a))
      = (G.trans hC t).rename Var.succ := by
  rw [← G.trans_rename hC t Var.succ, Ren.mapTy_shift]

theorem step_abs {Γ : List Ty} {a b : Ty} {A : Sequent S Γ} {s t : Term S (a :: Γ) b}
    (d : HistoryDerivation S es (G.transSeq hC
      { hyps := (weakenSequent (b := a) A).hyps, concl := s.equal t })) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) }) := by
  have hL : ∀ h, h ∈ G.ctxFix Γ →
      h ∈ (G.transSeq hC { hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) }).hyps :=
    fun h hh ↦ by simp [transSeq, hh]
  refine G.fromEq hC hw hL ?_
  -- the body equation, with the bound variable replaced by its normalisation
  have e0 := G.toEq hC hw (fun h hh ↦ by
      simp only [transSeq, List.mem_append]; exact Or.inl hh) d
  have e1 := HistoryDerivation.instTerm (Γ := (a :: Γ).map G.tr) (Δ := G.tr a :: Γ.map G.tr)
    (G.nrmSub a (Γ.map G.tr)) e0
  set Lt := (G.transSeq hC { hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) }).hyps
    with hLt
  set Lw : List (Term S (G.tr a :: Γ.map G.tr) .bool) := Lt.map (fun h ↦ h.rename Var.succ)
    with hLw
  have hH : ∀ h, h ∈ (termSubstSequent (G.nrmSub a (Γ.map G.tr))
      (G.transSeq hC { hyps := (weakenSequent (b := a) A).hyps, concl := s.equal t })).hyps →
      HistoryDerivation S es { hyps := Lw, concl := h } := by
    intro h hh
    simp only [termSubstSequent, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    simp only [transSeq, List.mem_append, List.mem_map] at hh0
    rcases hh0 with hh0 | ⟨w, hw', rfl⟩
    · rcases List.mem_cons.mp hh0 with rfl | ht
      · simp only [Term.substitute, G.nrmTy_substitute]
        exact G.nrmTy_idem hw a Lw _
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
        rw [G.ctxFix_tail_subst a t']
        exact HistoryDerivation.assume' _ (List.mem_map.mpr ⟨t', by simp [hLt, transSeq, ht'], rfl⟩)
    · simp only [weakenSequent, List.mem_map] at hw'
      obtain ⟨w', hw'', rfl⟩ := hw'
      simp only [weakenTerm]
      rw [G.trans_weaken hC hw w', G.ctxFix_tail_subst a (G.trans hC w')]
      exact HistoryDerivation.assume' _ (List.mem_map.mpr
        ⟨G.trans hC w', by simp only [hLt, transSeq, List.mem_append, List.mem_map]; exact Or.inr ⟨w', hw'', rfl⟩, rfl⟩)
  have e2 := HistoryDerivation.cutAll hH e1
  simp only [termSubstSequent, Term.substitute] at e2
  exact (HistoryDerivation.abs (A := { hyps := Lt, concl := Term.truth }) e2 :)

end Steps

theorem transS_ren {Γ Δ : List Ty} (r : Ren Γ Δ) {c : Ty} (w : Var (Γ.map G.tr) c) :
    Sub.transS G hC (fun {_} u ↦ (Term.var (r u) : Term S Δ _)) w
      = Term.var (Ren.mapTy G.tr r w) := by
  induction Γ generalizing Δ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => rfl
      | succ w => exact ih (fun u ↦ r (.succ u)) w

theorem transS_var (Γ : List Ty) {c : Ty} (w : Var (Γ.map G.tr) c) :
    Sub.transS G hC (fun {_} u ↦ (Term.var u : Term S Γ _)) w = Term.var w := by
  rw [G.transS_ren hC (fun {_} u ↦ u) w, Ren.mapTy_id]

theorem transS_single {Γ : List Ty} {a : Ty} (x : Term S Γ a) :
    @Eq (Sub S ((a :: Γ).map G.tr) (Γ.map G.tr)) (Sub.transS G hC (Sub.single x))
      (Sub.single (G.trans hC x)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w => exact G.transS_var hC Γ w

theorem nrm_single {Γ' : List Ty} {a c : Ty} (T : Term S (G.tr a :: Γ') c)
    (y : Term S Γ' (G.tr a)) :
    (T.substitute (G.nrmSub a Γ')).substitute (Sub.single y)
      = T.substitute (Sub.single (G.nrmTy a y)) := by
  rw [Term.substitute_substitute]
  congr 1
  funext c' v
  cases v with
  | zero =>
      change (G.nrmTy a (Term.var Var.zero)).substitute (Sub.single y) = G.nrmTy a y
      rw [G.nrmTy_substitute]; rfl
  | succ w => rfl

section Steps2

variable (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
include hw

theorem step_beta {Γ : List Ty} {a b : Ty} (s : Term S (a :: Γ) b) (x : Term S Γ a) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := [], concl := ((Term.lam s).app x).equal (s.substitute (Sub.single x)) }) := by
  refine G.fromEq hC hw (fun h hh ↦ by simp [transSeq, hh]) ?_
  rw [G.trans_substitute hC, G.transS_single hC]
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta ((G.trans hC s).substitute (G.nrmSub a (Γ.map G.tr))) (G.trans hC x))).mono
    (L := G.ctxFix Γ) (fun _ hh ↦ by simp at hh)
  rw [G.nrm_single] at b1
  have b2 := HistoryDerivation.leibniz (p := G.trans hC s) (G.trans_fixed hC hw x)
  exact (HistoryDerivation.trans' b1 b2).mono (fun h hh ↦ by simp [transSeq, hh])

theorem remove_trans {Γ : List Ty} (hs : List (Term S Γ .bool)) (c : Term S Γ .bool)
    (h : Term S (Γ.map G.tr) .bool)
    (hh : h ∈ remove (G.ctxFix Γ ++ hs.map (fun h0 ↦ (G.trans hC h0 : Term S (Γ.map G.tr) .bool)))
      (G.trans hC c : Term S (Γ.map G.tr) .bool)) :
    h ∈ G.ctxFix Γ ++ (remove hs c).map (fun h0 ↦ (G.trans hC h0 : Term S (Γ.map G.tr) .bool)) := by
  rw [mem_remove_iff] at hh
  obtain ⟨hh1, hh2⟩ := hh
  simp only [List.mem_append, List.mem_map] at hh1 ⊢
  rcases hh1 with hh1 | ⟨h0, hh0, rfl⟩
  · exact Or.inl hh1
  · refine Or.inr ⟨h0, ?_, rfl⟩
    rw [mem_remove_iff]
    exact ⟨hh0, fun e ↦ hh2 (by rw [e])⟩

theorem step_deduct {Γ : List Ty} {A B : Sequent S Γ}
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl),
        concl := A.concl.equal B.concl }) := by
  have hL : ∀ h, h ∈ G.ctxFix Γ → h ∈ (G.transSeq hC
      { hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl),
        concl := A.concl.equal B.concl }).hyps :=
    fun h hh ↦ by simp [transSeq, hh]
  refine G.fromEq hC hw hL ?_
  have := HistoryDerivation.deduct dA dB
  refine this.mono (fun h hh ↦ ?_)
  simp only [union, List.mem_append] at hh
  simp only [transSeq, union, List.map_append, List.mem_append]
  rcases hh with hh | hh
  · have := G.remove_trans hC hw A.hyps B.concl h hh
    simp only [List.mem_append] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have := G.remove_trans hC hw B.hyps A.concl h hh
    simp only [List.mem_append] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

end Steps2

theorem ctxFix_elem {Γ : List Ty} (h : Term S (Γ.map G.tr) .bool) (hh : h ∈ G.ctxFix Γ) :
    ∃ (a : Ty) (v : Var Γ a), h = (G.nrmTy a (Term.var (Var.mapTy G.tr v))).equal
      (Term.var (Var.mapTy G.tr v)) := by
  induction Γ with
  | nil => cases hh
  | cons x Γ ih =>
      rcases List.mem_cons.mp hh with rfl | ht
      · exact ⟨x, Var.zero, rfl⟩
      · obtain ⟨t, ht', rfl⟩ := List.mem_map.mp ht
        obtain ⟨a, v, rfl⟩ := ih t ht'
        refine ⟨a, Var.succ v, ?_⟩
        simp only [Term.rename, G.nrmTy_rename, Var.mapTy]

section Steps3

variable (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
include hw

theorem step_instTerm {Γ Δ : List Ty} {A : Sequent S Γ} (σ : Sub S Γ Δ)
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC (termSubstSequent σ A)) := by
  have e1 := HistoryDerivation.instTerm (Γ := Γ.map G.tr) (Δ := Δ.map G.tr)
    (Sub.transS G hC σ) d
  set L := (G.transSeq hC (termSubstSequent σ A)).hyps with hL
  have hH : ∀ h, h ∈ (termSubstSequent (Sub.transS G hC σ) (G.transSeq hC A)).hyps →
      HistoryDerivation S es { hyps := L, concl := h } := by
    intro h hh
    simp only [termSubstSequent, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    simp only [transSeq, List.mem_append, List.mem_map] at hh0
    rcases hh0 with hh0 | ⟨u, hu, rfl⟩
    · obtain ⟨a, v, rfl⟩ := G.ctxFix_elem h0 hh0
      simp only [Term.substitute, G.nrmTy_substitute]
      rw [G.transS_apply hC σ v]
      exact (G.trans_fixed hC hw (σ v)).mono (fun h' hh' ↦ by
        simp only [hL, transSeq, List.mem_append]; exact Or.inl hh')
    · rw [← G.trans_substitute hC u σ]
      exact HistoryDerivation.assume' _ (by
        simp only [hL, transSeq, termSubstSequent, List.mem_append, List.mem_map]
        exact Or.inr ⟨u.substitute σ, ⟨u, hu, rfl⟩, rfl⟩)
  have e2 := HistoryDerivation.cutAll hH e1
  simp only [termSubstSequent, transSeq] at e2 ⊢
  rw [← G.trans_substitute hC A.concl σ] at e2
  exact e2

theorem step_chooseHyp {Γ : List Ty} {a : Ty} {A : Sequent S Γ} (p : Term S (a :: Γ) .bool)
    (wt : Term S Γ a) (hA : A.concl = p.substitute (Sub.single wt))
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := p.substitute (Sub.single (Term.choice.app (Term.lam p))) }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  set L := (G.transSeq hC { hyps := hA', concl := p.substitute (Sub.single wt) }).hyps with hL
  have hLc : ∀ h, h ∈ G.ctxFix Γ → h ∈ L := fun h hh ↦ by simp [hL, transSeq, hh]
  set Tp := G.trans hC p with hTp
  set Tw := G.trans hC wt with hTw
  set q := Tp.substitute (G.nrmSub a (Γ.map G.tr)) with hq
  have hfix := (G.trans_fixed hC hw wt).mono hLc
  -- the witness for the normalised body
  have d1 : HistoryDerivation S es { hyps := L, concl := Tp.substitute (Sub.single Tw) } := by
    have := d
    simp only [transSeq] at this
    rw [G.trans_substitute hC, G.transS_single hC] at this
    exact this
  have d2 : HistoryDerivation S es
      { hyps := L, concl := q.substitute (Sub.single Tw) } := by
    rw [hq, G.nrm_single]
    exact HistoryDerivation.eqMp'
      (HistoryDerivation.sym (HistoryDerivation.leibniz (p := Tp) hfix)) d1
  have raw := HistoryDerivation.chooseHyp (es := es)
    (A := { hyps := L, concl := q.substitute (Sub.single Tw) }) q Tw rfl d2
  simp only [hq, G.nrm_single] at raw
  -- the translated choice term is the normalised choice term of the body
  have m1 := G.nrm_app (.arr a .bool) a (L := L)
    (Term.choice : Term S _ (G.tr (.arr (.arr a .bool) a))) (Term.lam q) (es := es)
  have m2 := (G.trans_fixed hC hw (Term.lam p)).mono hLc
  have m3 := G.nrmTy_congr a (HistoryDerivation.mkComb'
    (HistoryDerivation.refl' (L := L) (Term.choice : Term S _ (G.tr (.arr (.arr a .bool) a)))) m2)
  have hε := HistoryDerivation.trans' m1 m3
  have key := HistoryDerivation.leibniz (p := Tp) hε
  have goal := HistoryDerivation.eqMp' (HistoryDerivation.sym key) raw
  simp only [transSeq]
  rw [G.trans_substitute hC, G.transS_single hC]
  exact goal

theorem step_truthIntro {Γ : List Ty} :
    HistoryDerivation S es (G.transSeq hC ({ hyps := [], concl := Term.truth } : Sequent S Γ)) :=
  HistoryDerivation.truthIntro.mono (fun _ hh ↦ by simp at hh)

theorem step_falsityElim {Γ : List Ty} {A : Sequent S Γ} (q : Term S Γ .bool)
    (hA : A.concl = Term.falsity) (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := q }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  exact HistoryDerivation.falsityElim (G.trans hC q) rfl d

theorem step_conjIntro {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = p) (hB : B.concl = q)
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := union A.hyps B.hyps, concl := Term.conj p q }) := by
  cases A with | mk hA' cA => cases B with | mk hB' cB =>
  simp only at hA hB; subst hA; subst hB
  exact HistoryDerivation.conjI
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_left _ hh) dA)
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_right _ hh) dB)

theorem step_conjElimLeft {Γ : List Ty} {A : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := p }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  exact HistoryDerivation.conjL d

theorem step_conjElimRight {Γ : List Ty} {A : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := q }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  exact HistoryDerivation.conjR d

theorem step_impIntro {Γ : List Ty} {A : Sequent S Γ} (p : Term S Γ .bool)
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := remove A.hyps p, concl := Term.imp p A.concl }) := by
  have := HistoryDerivation.impIntro (G.trans hC p) d
  refine this.mono (fun h hh ↦ ?_)
  have := G.remove_trans hC hw A.hyps p h hh
  simpa [transSeq] using this

theorem step_impElim {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.imp p q) (hB : B.concl = p)
    (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC B)) :
    HistoryDerivation S es (G.transSeq hC { hyps := union A.hyps B.hyps, concl := q }) := by
  cases A with | mk hA' cA => cases B with | mk hB' cB =>
  simp only at hA hB; subst hA; subst hB
  exact HistoryDerivation.mp
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_left _ hh) dA)
    (G.step_weakenHyps hC hw (union hA' hB') (fun h hh ↦ List.mem_append_right _ hh) dB)

theorem step_classical {Γ : List Ty} {A : Sequent S Γ} {p : Term S Γ .bool}
    (hA : A.concl = Term.imp (Term.imp p Term.falsity) Term.falsity)
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := p }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  exact HistoryDerivation.classical rfl d

/-- A derivation in the extended context, instantiated at the normalised bound variable. -/
theorem body_inst {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (c : Term S Γ .bool)
    (d : HistoryDerivation S es (G.transSeq hC
      { hyps := (weakenSequent (b := a) A).hyps, concl := φ })) :
    HistoryDerivation S es
      { hyps := (G.transSeq hC { hyps := A.hyps, concl := c }).hyps.map
          (fun h ↦ h.rename Var.succ),
        concl := (G.trans hC φ).substitute (G.nrmSub a (Γ.map G.tr)) } := by
  have e1 := HistoryDerivation.instTerm (Γ := (a :: Γ).map G.tr) (Δ := G.tr a :: Γ.map G.tr)
    (G.nrmSub a (Γ.map G.tr)) d
  set Lt := (G.transSeq hC { hyps := A.hyps, concl := c }).hyps with hLt
  set Lw : List (Term S (G.tr a :: Γ.map G.tr) .bool) := Lt.map (fun h ↦ h.rename Var.succ)
    with hLw
  have hH : ∀ h, h ∈ (termSubstSequent (G.nrmSub a (Γ.map G.tr))
      (G.transSeq hC { hyps := (weakenSequent (b := a) A).hyps, concl := φ })).hyps →
      HistoryDerivation S es { hyps := Lw, concl := h } := by
    intro h hh
    simp only [termSubstSequent, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    simp only [transSeq, List.mem_append, List.mem_map] at hh0
    rcases hh0 with hh0 | ⟨w', hw', rfl⟩
    · rcases List.mem_cons.mp hh0 with rfl | ht
      · simp only [Term.substitute, G.nrmTy_substitute]
        exact G.nrmTy_idem hw a Lw _
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
        rw [G.ctxFix_tail_subst a t']
        exact HistoryDerivation.assume' _ (List.mem_map.mpr ⟨t', by simp [hLt, transSeq, ht'], rfl⟩)
    · simp only [weakenSequent, List.mem_map] at hw'
      obtain ⟨w'', hw'', rfl⟩ := hw'
      simp only [weakenTerm]
      rw [G.trans_weaken hC hw w'', G.ctxFix_tail_subst a (G.trans hC w'')]
      exact HistoryDerivation.assume' _ (List.mem_map.mpr
        ⟨G.trans hC w'', by simp only [hLt, transSeq, List.mem_append, List.mem_map]; exact Or.inr ⟨w'', hw'', rfl⟩, rfl⟩)
  have e2 := HistoryDerivation.cutAll hH e1
  simp only [termSubstSequent, transSeq] at e2
  exact e2

theorem step_allIntro {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (d : HistoryDerivation S es (G.transSeq hC
      { hyps := (weakenSequent (b := a) A).hyps, concl := φ })) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := Term.all φ }) :=
  HistoryDerivation.allIntro (A := { hyps := (G.transSeq hC
    { hyps := A.hyps, concl := Term.all φ }).hyps, concl := Term.truth })
    (G.body_inst hC hw (Term.all φ) d)

theorem step_allElim {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (t : Term S Γ a) (hA : A.concl = Term.all φ)
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC
      { hyps := A.hyps, concl := φ.substitute (Sub.single t) }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  have h1 := HistoryDerivation.allElim (G.trans hC t) rfl d
  simp only [transSeq] at h1 ⊢
  rw [G.nrm_single] at h1
  rw [G.trans_substitute hC, G.transS_single hC]
  have hLc : ∀ h, h ∈ G.ctxFix Γ → h ∈ G.ctxFix Γ ++ hA'.map (fun h ↦ (G.trans hC h : Term S (Γ.map G.tr) .bool)) :=
    fun h hh ↦ List.mem_append_left _ hh
  exact HistoryDerivation.eqMp' (HistoryDerivation.leibniz (p := G.trans hC φ)
    ((G.trans_fixed hC hw t).mono hLc)) h1

theorem step_exIntro {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (t : Term S Γ a) (hA : A.concl = φ.substitute (Sub.single t))
    (d : HistoryDerivation S es (G.transSeq hC A)) :
    HistoryDerivation S es (G.transSeq hC { hyps := A.hyps, concl := Term.ex φ }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  simp only [transSeq] at d ⊢
  rw [G.trans_substitute hC, G.transS_single hC] at d
  have hLc : ∀ h, h ∈ G.ctxFix Γ → h ∈ G.ctxFix Γ ++ hA'.map (fun h ↦ (G.trans hC h : Term S (Γ.map G.tr) .bool)) :=
    fun h hh ↦ List.mem_append_left _ hh
  have d2 := HistoryDerivation.eqMp'
    (HistoryDerivation.sym (HistoryDerivation.leibniz (p := G.trans hC φ)
      ((G.trans_fixed hC hw t).mono hLc))) d
  rw [← G.nrm_single] at d2
  exact HistoryDerivation.exIntro (G.trans hC t) rfl d2

theorem step_exElim {Γ : List Ty} {a : Ty} {A B : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (hA : A.concl = Term.ex φ) (dA : HistoryDerivation S es (G.transSeq hC A))
    (dB : HistoryDerivation S es (G.transSeq hC
      { hyps := φ :: (weakenSequent (b := a) B).hyps, concl := weakenTerm B.concl })) :
    HistoryDerivation S es (G.transSeq hC { hyps := union A.hyps B.hyps, concl := B.concl }) := by
  cases A with | mk hA' cA =>
  simp only at hA; subst hA
  set LB := (G.transSeq hC B).hyps with hLB
  set Lw : List (Term S (G.tr a :: Γ.map G.tr) .bool) := LB.map (fun h ↦ h.rename Var.succ)
    with hLw
  have e1 := HistoryDerivation.instTerm (Γ := (a :: Γ).map G.tr) (Δ := G.tr a :: Γ.map G.tr)
    (G.nrmSub a (Γ.map G.tr)) dB
  have hH : ∀ h, h ∈ (termSubstSequent (G.nrmSub a (Γ.map G.tr)) (G.transSeq hC
      { hyps := φ :: (weakenSequent (b := a) B).hyps, concl := weakenTerm B.concl })).hyps →
      HistoryDerivation S es { hyps := (G.trans hC φ).substitute (G.nrmSub a (Γ.map G.tr)) :: Lw, concl := h } := by
    intro h hh
    simp only [termSubstSequent, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    simp only [transSeq, List.mem_append, List.mem_map, List.mem_cons] at hh0
    rcases hh0 with hh0 | ⟨u, hu, rfl⟩
    · rcases List.mem_cons.mp hh0 with rfl | ht
      · simp only [Term.substitute, G.nrmTy_substitute]
        exact G.nrmTy_idem hw a _ _
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
        rw [G.ctxFix_tail_subst a t']
        exact HistoryDerivation.assume' _ (List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨t', by simp [hLB, transSeq, ht'], rfl⟩))
    · rcases hu with rfl | hu
      · exact HistoryDerivation.assume' _ (List.mem_cons_self ..)
      · simp only [weakenSequent, List.mem_map] at hu
        obtain ⟨w'', hw'', rfl⟩ := hu
        simp only [weakenTerm]
        rw [G.trans_weaken hC hw w'', G.ctxFix_tail_subst a (G.trans hC w'')]
        exact HistoryDerivation.assume' _ (List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨G.trans hC w'', by simp only [hLB, transSeq, List.mem_append, List.mem_map]; exact Or.inr ⟨w'', hw'', rfl⟩, rfl⟩))
  have e2 := HistoryDerivation.cutAll hH e1
  simp only [termSubstSequent, transSeq, weakenTerm] at e2
  rw [G.trans_weaken hC hw B.concl, G.ctxFix_tail_subst a (G.trans hC B.concl)] at e2
  have e3 := HistoryDerivation.exElim (es := es)
    (A := { hyps := (G.transSeq hC { hyps := hA', concl := Term.ex φ }).hyps,
            concl := G.trans hC (Term.ex φ) })
    (B := { hyps := LB, concl := G.trans hC B.concl }) rfl dA e2
  refine e3.mono (fun h hh ↦ ?_)
  simp only [union, List.mem_append] at hh
  rcases hh with hh | hh
  · simp only [transSeq, union, List.mem_append, List.mem_map] at hh ⊢
    rcases hh with hh | ⟨u, hu, rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨u, Or.inl hu, rfl⟩
  · rw [hLB] at hh
    simp only [transSeq, union, List.mem_append, List.mem_map] at hh ⊢
    rcases hh with hh | ⟨u, hu, rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨u, Or.inr hu, rfl⟩

end Steps3

end TypeDefGate

end QEDFV.HOL
