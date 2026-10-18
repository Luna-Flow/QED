import QEDFV.HOL.TdLaw

/-! The translation of derivations: every derivation at a history without definitions is
translated, at every type instance, to a derivation at the history before the type
definition. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QEDFV.HOL

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {es : List (ModelExtension S)}

/-- The weakened hypotheses commute with type instantiation. -/
theorem weaken_inst {Γ : List Ty} {a : Ty} (A : Sequent S Γ) (θ : TypeSub) :
    (weakenSequent (b := a) A).hyps.map (fun h ↦ h.instType θ)
      = (weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps := by
  simp only [weakenSequent, typeSubstSequent, List.map_map]
  apply List.map_congr_left
  intro h _
  simp only [Function.comp, weakenTerm]
  rw [Term.rename_instType, Ren.mapTypes_shift]

theorem transSeq_of_eq {Γ : List Ty} (hC : G.Closed) {s s' : Sequent S Γ} (e : s = s')
    (d : HistoryDerivation S es (G.transSeq hC s)) : HistoryDerivation S es (G.transSeq hC s') :=
  e ▸ d

theorem transSeq_heq {Γ1 Γ2 : List Ty} (hC : G.Closed) (e : Γ1 = Γ2) {s1 : Sequent S Γ1}
    {s2 : Sequent S Γ2} (hs : HEq s1 s2) (d : HistoryDerivation S es (G.transSeq hC s1)) :
    HistoryDerivation S es (G.transSeq hC s2) := by
  subst e
  have := eq_of_heq hs
  subst this
  exact d

theorem transSeq_mono {Γ : List Ty} (hC : G.Closed) {s1 s2 : Sequent S Γ}
    (hc : s1.concl = s2.concl) (hh : ∀ h, h ∈ s1.hyps → h ∈ s2.hyps)
    (d : HistoryDerivation S es (G.transSeq hC s1)) :
    HistoryDerivation S es (G.transSeq hC s2) := by
  have := d.mono (L := (G.transSeq hC s2).hyps) (fun h hm ↦ by
    simp only [transSeq, List.mem_append, List.mem_map] at hm ⊢
    rcases hm with hm | ⟨u, hu, rfl⟩
    · exact Or.inl hm
    · exact Or.inr ⟨u, hh u hu, rfl⟩)
  simp only [transSeq, hc] at this ⊢
  exact this

theorem weakenTerm_inst {Γ : List Ty} {a b : Ty} (t : Term S Γ a) (θ : TypeSub) :
    (weakenTerm (b := b) t).instType θ = weakenTerm (b := b.subst θ) (t.instType θ) := by
  simp only [weakenTerm]
  rw [Term.rename_instType, Ren.mapTypes_shift]

theorem remove_map_sub {α β : Type _} (f : α → β) (xs : List α) (c : α) (h : β)
    (hh : h ∈ remove (xs.map f) (f c)) : h ∈ (remove xs c).map f := by
  classical
  simp only [remove, List.mem_filter, List.mem_map] at hh ⊢
  obtain ⟨⟨a, ha, rfl⟩, hne⟩ := hh
  refine ⟨a, ⟨ha, ?_⟩, rfl⟩
  by_cases e : a = c
  · subst e; simp at hne
  · simp [e]

theorem trans_sentence (hC : G.Closed) (θ : TypeSub) :
    (G.trans hC ((indInfinitySentence S).instType θ) : Term S [] .bool) = indInfinitySentence S := by
  have hk : G.k ∉ (indInfinitySentence S).tyCons := by
    simp [indInfinitySentence, indInjectiveBody, indNonSurjectiveBody, Term.tyCons, Ty.tyCons]
  have hs : (indInfinitySentence S).SigClean G.k := by
    simp [indInfinitySentence, indInjectiveBody, indNonSurjectiveBody, Term.SigClean, Term.equal]
  have hg : (indInfinitySentence S).annotVars = ∅ := by
    simp [indInfinitySentence, indInjectiveBody, indNonSurjectiveBody, Term.annotVars, Ty.typeVars,
      Term.equal]
  exact eq_of_heq (Term.erase_inj_heq' _ _ rfl rfl (G.erase_trans_inst hC _ hk hs hg θ))

section Core

variable (hOk : G.Ok) {w : Term S [] G.repTy}
  (hwit : HistoryDerivation S es { hyps := [], concl := G.pred.app w })
include hOk hwit

/-- Core derivations translate at every type instance. -/
theorem core_trans {Γ : List Ty} {s : Sequent S Γ} (d : Derivation S s) (θ : TypeSub) :
    HistoryDerivation S es (G.transSeq hOk.closed (typeSubstSequent θ s)) := by
  induction d generalizing θ with
  | refl t => exact G.step_refl hOk.closed hwit (t.instType θ)
  | assume p => exact G.step_assume hOk.closed hwit (p.instType θ)
  | addAssum p d ih => exact G.step_addAssum hOk.closed hwit (p.instType θ) (ih θ)
  | @trans Γ a A B x y z hA hB dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (y.instType θ).equal (z.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_trans hOk.closed hwit hA' hB' (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @mkComb Γ a b A B f g x y hA hB dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = (f.instType θ).equal (g.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_mkComb hOk.closed hwit hA' hB' (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @abs Γ a b A s t d ih =>
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, s.equal t⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            (s.instType θ).equal (t.instType θ)⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_abs hOk.closed hwit (G.transSeq_of_eq hOk.closed e (ih θ))
  | @beta Γ a b s x =>
      have := G.step_beta hOk.closed hwit (s.instType θ) (x.instType θ)
      refine G.transSeq_of_eq hOk.closed ?_ this
      simp only [typeSubstSequent, List.map_nil]
      congr 1
      exact (congrArg (fun t ↦ ((s.instType θ).lam.app (x.instType θ)).equal t)
        (Term.instType_single s x θ)).symm
  | @eqMp Γ A B p q hA hB dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = (p.instType θ).equal (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_eqMp hOk.closed hwit hA' hB' (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @deduct Γ A B dA dB ihA ihB =>
      have step := G.step_deduct hOk.closed hwit (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (remove_map_sub (fun h ↦ h.instType θ) A.hyps B.concl h hh)
        · exact Or.inr (remove_map_sub (fun h ↦ h.instType θ) B.hyps A.concl h hh)
  | @instType Γ A θ' d ih =>
      exact G.transSeq_heq hOk.closed (ctx_map_comp Γ θ' θ).symm
        (typeSubstSequent_comp A θ' θ).symm (ih (θ.comp θ'))
  | @instTerm Γ Δ A σ d ih =>
      have step := G.step_instTerm hOk.closed hwit (Sub.mapTypes θ σ) (ih θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [termSubstSequent, typeSubstSequent, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro h _
        exact (Term.substitute_instType h σ θ).symm
      · exact (Term.substitute_instType _ σ θ).symm
  | @chooseWitness Γ a p w d ih =>
      have hA' : (typeSubstSequent θ (⟨[], p.substitute (Sub.single w)⟩ : Sequent S Γ)).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [Term.instType_single]
      have step := G.step_chooseHyp hOk.closed hwit (p.instType θ) (w.instType θ) hA' (ih θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent, List.map_nil]
      congr 1
      rw [Term.instType_single]
      rfl
  | indInfinity =>
      have := (HistoryDerivation.core (es := es) (Derivation.indInfinity)).mono
        (L := (G.transSeq hOk.closed (typeSubstSequent θ
          (⟨[], indInfinitySentence S⟩ : Sequent S ([] : List Ty)))).hyps) (fun h hh ↦ by simp at hh)
      simp only [transSeq, typeSubstSequent, List.map_nil, trans_sentence] at this ⊢
      exact this
  | truthIntro => exact G.step_truthIntro hOk.closed hwit
  | @falsityElim Γ A q hA d ih =>
      have hA' : (typeSubstSequent θ A).concl = Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_falsityElim hOk.closed hwit (q.instType θ) hA' (ih θ)
  | @conjIntro Γ A B p q hA hB dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hA]
      have hB' : (typeSubstSequent θ B).concl = q.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_conjIntro hOk.closed hwit hA' hB' (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @conjElimLeft Γ A p q hA d ih =>
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimLeft hOk.closed hwit hA' (ih θ)
  | @conjElimRight Γ A p q hA d ih =>
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimRight hOk.closed hwit hA' (ih θ)
  | @impIntro Γ A p d ih =>
      have step := G.step_impIntro hOk.closed hwit (p.instType θ) (ih θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [typeSubstSequent] at hh ⊢
        exact remove_map_sub (fun h ↦ h.instType θ) A.hyps p h hh
  | @impElim Γ A B p q hA hB dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = Term.imp (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_impElim hOk.closed hwit hA' hB' (ihA θ) (ihB θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @allIntro Γ a A φ d ih =>
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, φ⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            φ.instType θ⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_allIntro hOk.closed hwit (G.transSeq_of_eq hOk.closed e (ih θ))
  | @allElim Γ a A φ t hA d ih =>
      have hA' : (typeSubstSequent θ A).concl = Term.all (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have step := G.step_allElim hOk.closed hwit (t.instType θ) hA' (ih θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent]
      rw [Term.instType_single]
  | @exIntro Γ a A φ t hA d ih =>
      have hA' : (typeSubstSequent θ A).concl
          = (φ.instType θ).substitute (Sub.single (t.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      exact G.step_exIntro hOk.closed hwit (t.instType θ) hA' (ih θ)
  | @exElim Γ a A B φ hA dA dB ihA ihB =>
      have hA' : (typeSubstSequent θ A).concl = Term.ex (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have e : typeSubstSequent θ (⟨φ :: (weakenSequent (b := a) B).hyps, weakenTerm B.concl⟩ :
          Sequent S (a :: Γ)) = ⟨φ.instType θ :: (weakenSequent (b := a.subst θ)
            (typeSubstSequent θ B)).hyps, weakenTerm (b := a.subst θ) (B.concl.instType θ)⟩ := by
        simp only [typeSubstSequent, List.map_cons]
        congr 1
        · congr 1
          exact weaken_inst B θ
        · exact weakenTerm_inst B.concl θ
      have step := G.step_exElim hOk.closed hwit hA' (ihA θ) (G.transSeq_of_eq hOk.closed e (ihB θ))
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @classical Γ A p hA d ih =>
      have hA' : (typeSubstSequent θ A).concl
          = Term.imp (Term.imp (p.instType θ) Term.falsity) Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_classical hOk.closed hwit hA' (ih θ)
  | @chooseHyp Γ a A p w hA d ih =>
      have hA' : (typeSubstSequent θ A).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      have step := G.step_chooseHyp hOk.closed hwit (p.instType θ) (w.instType θ) hA' (ih θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent]
      congr 1
      rw [Term.instType_single]
      rfl

end Core

section Main

variable (hOk : G.Ok) {w : Term S [] G.repTy}
  (hwit : HistoryDerivation S ([] : List (ModelExtension S))
    { hyps := [], concl := G.pred.app w })
include hOk hwit

/-- The history is the empty history or the history with the single type definition. -/
def HistOk (h : List (ModelExtension S)) : Prop := h = [] ∨ h = [ModelExtension.typeDefinition G]

theorem ext_trans {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) (hh : G.HistOk h) (θ : TypeSub) :
    HistoryDerivation S [] (G.transSeq hOk.closed (typeSubstSequent θ s)) := by
  revert hh θ
  induction d with
  | core d => exact fun _ θ ↦ G.core_trans hOk hwit d θ
  | @weaken es' Γ s e d hOld ih =>
      intro hh θ
      rcases hh with hh | hh
      · simp at hh
      · exact ih (Or.inl (List.cons.inj hh).2) θ
  | definition D hFresh => intro hh; rcases hh with hh | hh <;> simp at hh
  | specification E hFresh d ih => intro hh; rcases hh with hh | hh <;> simp at hh
  | typedef G' l hk hrep habs w' d' ih =>
      intro hh θ
      rcases hh with hh | hh
      · simp at hh
      · obtain ⟨hG, _⟩ := List.cons.inj hh
        cases hG
        cases l with
        | absRep => exact G.trans_law1 hOk θ hwit
        | repRange => exact G.trans_law2 hOk θ hwit
        | repAbs => exact G.trans_law3 hOk θ hwit


theorem hd_trans {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) (hh : G.HistOk h) (θ : TypeSub) :
    HistoryDerivation S [] (G.transSeq hOk.closed (typeSubstSequent θ s)) := by
  revert hh θ
  induction d with
  | core d => exact fun _ θ ↦ G.core_trans hOk hwit d θ
  | extension d => exact fun hh θ ↦ G.ext_trans hOk hwit d hh θ
  | @weaken es' Γ s e d hOld ih =>
      intro hh θ
      rcases hh with hh | hh
      · simp at hh
      · exact ih (Or.inl (List.cons.inj hh).2) θ
  | definition D hFresh => intro hh; rcases hh with hh | hh <;> simp at hh
  | specification E hFresh d ih => intro hh; rcases hh with hh | hh <;> simp at hh
  | typedef G' l hk hrep habs w' d' ih =>
      intro hh θ
      rcases hh with hh | hh
      · simp at hh
      · obtain ⟨hG, _⟩ := List.cons.inj hh
        cases hG
        cases l with
        | absRep => exact G.trans_law1 hOk θ hwit
        | repRange => exact G.trans_law2 hOk θ hwit
        | repAbs => exact G.trans_law3 hOk θ hwit
  | @weakenHyps es' Γ A L hL d ih =>
      intro hh θ
      refine G.transSeq_mono hOk.closed ?_ ?_ (ih hh θ)
      · rfl
      · intro x hx
        simp only [typeSubstSequent, List.mem_map] at hx ⊢
        obtain ⟨u, hu, rfl⟩ := hx
        exact ⟨u, hL u hu, rfl⟩
  | addAssum p d ih =>
      intro hh θ
      exact G.step_addAssum hOk.closed hwit (p.instType θ) (ih hh θ)
  | @trans es' Γ a A B x y z hA hB dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (y.instType θ).equal (z.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_trans hOk.closed hwit hA' hB' (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @mkComb es' Γ a b A B f g x y hA hB dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = (f.instType θ).equal (g.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_mkComb hOk.closed hwit hA' hB' (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @abs es' Γ a b A s t d ih =>
      intro hh θ
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, s.equal t⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            (s.instType θ).equal (t.instType θ)⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_abs hOk.closed hwit (G.transSeq_of_eq hOk.closed e (ih hh θ))
  | @eqMp es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = (p.instType θ).equal (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_eqMp hOk.closed hwit hA' hB' (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @deduct es' Γ A B dA dB ihA ihB =>
      intro hh θ
      have step := G.step_deduct hOk.closed hwit (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (remove_map_sub (fun h ↦ h.instType θ) A.hyps B.concl h hh)
        · exact Or.inr (remove_map_sub (fun h ↦ h.instType θ) B.hyps A.concl h hh)
  | @instType es' Γ A θ' d ih =>
      intro hh θ
      exact G.transSeq_heq hOk.closed (ctx_map_comp Γ θ' θ).symm
        (typeSubstSequent_comp A θ' θ).symm (ih hh (θ.comp θ'))
  | @instTerm es' Γ Δ A σ d ih =>
      intro hh θ
      have step := G.step_instTerm hOk.closed hwit (Sub.mapTypes θ σ) (ih hh θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [termSubstSequent, typeSubstSequent, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro h _
        exact (Term.substitute_instType h σ θ).symm
      · exact (Term.substitute_instType _ σ θ).symm
  | @chooseWitness es' Γ a p w d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ (⟨[], p.substitute (Sub.single w)⟩ : Sequent S Γ)).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [Term.instType_single]
      have step := G.step_chooseHyp hOk.closed hwit (p.instType θ) (w.instType θ) hA' (ih hh θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent, List.map_nil]
      congr 1
      rw [Term.instType_single]
      rfl
  | truthIntro =>
      intro hh θ
      exact G.step_truthIntro hOk.closed hwit
  | @falsityElim es' Γ A q hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_falsityElim hOk.closed hwit (q.instType θ) hA' (ih hh θ)
  | @conjIntro es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hA]
      have hB' : (typeSubstSequent θ B).concl = q.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_conjIntro hOk.closed hwit hA' hB' (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @conjElimLeft es' Γ A p q hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimLeft hOk.closed hwit hA' (ih hh θ)
  | @conjElimRight es' Γ A p q hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimRight hOk.closed hwit hA' (ih hh θ)
  | @impIntro es' Γ A p d ih =>
      intro hh θ
      have step := G.step_impIntro hOk.closed hwit (p.instType θ) (ih hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [typeSubstSequent] at hh ⊢
        exact remove_map_sub (fun h ↦ h.instType θ) A.hyps p h hh
  | @impElim es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.imp (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_impElim hOk.closed hwit hA' hB' (ihA hh θ) (ihB hh θ)
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @allIntro es' Γ a A φ d ih =>
      intro hh θ
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, φ⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            φ.instType θ⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_allIntro hOk.closed hwit (G.transSeq_of_eq hOk.closed e (ih hh θ))
  | @allElim es' Γ a A φ t hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.all (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have step := G.step_allElim hOk.closed hwit (t.instType θ) hA' (ih hh θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent]
      rw [Term.instType_single]
  | @exIntro es' Γ a A φ t hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl
          = (φ.instType θ).substitute (Sub.single (t.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      exact G.step_exIntro hOk.closed hwit (t.instType θ) hA' (ih hh θ)
  | @exElim es' Γ a A B φ hA dA dB ihA ihB =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl = Term.ex (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have e : typeSubstSequent θ (⟨φ :: (weakenSequent (b := a) B).hyps, weakenTerm B.concl⟩ :
          Sequent S (a :: Γ)) = ⟨φ.instType θ :: (weakenSequent (b := a.subst θ)
            (typeSubstSequent θ B)).hyps, weakenTerm (b := a.subst θ) (B.concl.instType θ)⟩ := by
        simp only [typeSubstSequent, List.map_cons]
        congr 1
        · congr 1
          exact weaken_inst B θ
        · exact weakenTerm_inst B.concl θ
      have step := G.step_exElim hOk.closed hwit hA' (ihA hh θ) (G.transSeq_of_eq hOk.closed e (ihB hh θ))
      refine G.transSeq_mono hOk.closed ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @classical es' Γ A p hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl
          = Term.imp (Term.imp (p.instType θ) Term.falsity) Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_classical hOk.closed hwit hA' (ih hh θ)
  | @chooseHyp es' Γ a A p w hA d ih =>
      intro hh θ
      have hA' : (typeSubstSequent θ A).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      have step := G.step_chooseHyp hOk.closed hwit (p.instType θ) (w.instType θ) hA' (ih hh θ)
      refine G.transSeq_of_eq hOk.closed ?_ step
      simp only [typeSubstSequent]
      congr 1
      rw [Term.instType_single]
      rfl

end Main

end TypeDefGate

end QEDFV.HOL

namespace QEDFV.HOL

theorem Var.mem {Γ : List Ty} {a : Ty} (v : Var Γ a) : a ∈ Γ := by
  induction v with
  | zero => exact List.mem_cons_self ..
  | succ v ih => exact List.mem_cons_of_mem _ ih

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

theorem ctx_tr_var (Γ : List Ty) (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) :
    (Γ.map (Ty.subst Ty.var)).map G.tr = Γ := by
  induction Γ with
  | nil => rfl
  | cons b Γ ih =>
      simp only [List.map_cons, Ty.subst_id]
      rw [G.tr_kfree (hΓ b (List.mem_cons_self ..)),
        ih (fun b' hb' ↦ hΓ b' (List.mem_cons_of_mem _ hb'))]

theorem trans_inst_var_heq (hC : G.Closed) {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hk : G.k ∉ t.tyCons) (hs : t.SigClean G.k)
    (e : (Γ.map (Ty.subst Ty.var)).map G.tr = Γ) (ha : G.tr (a.subst Ty.var) = a) :
    HEq (G.trans hC (t.instType Ty.var)) t :=
  Term.erase_inj_heq' _ _ e ha (G.erase_trans_var hC t hk hs)

/-- Transport of a derivation along a context equality, discharging reflexive hypotheses. -/
theorem final_transport {Γ1 Γ : List Ty} (e : Γ1 = Γ) (s1 : Sequent S Γ1) (s : Sequent S Γ)
    (hconcl : HEq s1.concl s.concl)
    (hhyps : ∀ h, h ∈ s1.hyps → (∃ h0, h0 ∈ s.hyps ∧ HEq h h0) ∨
      ∃ (a : Ty) (x : Term S Γ1 a), h = x.equal x)
    (hback : ∀ h0, h0 ∈ s.hyps → ∃ h, h ∈ s1.hyps ∧ HEq h h0)
    (d : HistoryDerivation S ([] : List (ModelExtension S)) s1) :
    HistoryDerivation S ([] : List (ModelExtension S)) s := by
  subst e
  have hc := eq_of_heq hconcl
  have d2 : HistoryDerivation S ([] : List (ModelExtension S))
      { hyps := s.hyps, concl := s1.concl } := by
    refine HistoryDerivation.cutAll (H := s1.hyps) (fun h hh ↦ ?_) d
    rcases hhyps h hh with ⟨h0, h0m, hh0⟩ | ⟨a, x, rfl⟩
    · rw [eq_of_heq hh0]; exact HistoryDerivation.assume' _ h0m
    · exact HistoryDerivation.refl' x
  rw [hc] at d2
  exact d2

end TypeDefGate

end QEDFV.HOL

namespace QEDFV.HOL

/-- A sequent whose types avoid the constructor `k` and whose constants carry canonical
instance substitutions. -/
def Sequent.Clean {S : Signature} {Γ : List Ty} (k : Nat) (s : Sequent S Γ) : Prop :=
  (∀ h, h ∈ s.hyps → k ∉ h.tyCons ∧ h.SigClean k) ∧ k ∉ s.concl.tyCons ∧ s.concl.SigClean k

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- **Syntactic conservativity of a type definition** (a type definition without parameters
over the empty history): a sequent in the old language that is derivable after the type
definition is derivable before it, provided the predicate has a derivable witness. -/
theorem typedef_conservative (hOk : G.Ok) {Γ : List Ty} {s : Sequent S Γ}
    (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) (hclean : s.Clean G.k) {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S ([] : List (ModelExtension S))
      { hyps := [], concl := G.pred.app w })
    (d : HistoryDerivation S [ModelExtension.typeDefinition G] s) :
    HistoryDerivation S ([] : List (ModelExtension S)) s := by
  have d1 := G.hd_trans hOk hwit d (Or.inr rfl) Ty.var
  have e := G.ctx_tr_var Γ hΓ
  refine final_transport e _ s ?_ ?_ ?_ d1
  · exact G.trans_inst_var_heq hOk.closed s.concl hclean.2.1 hclean.2.2 e rfl
  · intro h hh
    simp only [transSeq, typeSubstSequent, List.mem_append, List.mem_map] at hh
    rcases hh with hh | ⟨u, ⟨h0, hh0, rfl⟩, rfl⟩
    · right
      obtain ⟨a, v, rfl⟩ := G.ctxFix_elem h hh
      have ha : G.k ∉ a.tyCons := by
        have hm := Var.mem v
        simp only [List.mem_map] at hm
        obtain ⟨b, hb, rfl⟩ := hm
        rw [Ty.subst_id]; exact hΓ b hb
      refine ⟨G.tr a, Term.var (Var.mapTy G.tr v), ?_⟩
      rw [G.nrmTy_of_not_mem a ha]
    · left
      exact ⟨h0, hh0, G.trans_inst_var_heq hOk.closed h0 (hclean.1 h0 hh0).1 (hclean.1 h0 hh0).2 e rfl⟩
  · intro h0 hh0
    refine ⟨G.trans hOk.closed (h0.instType Ty.var), ?_,
      G.trans_inst_var_heq hOk.closed h0 (hclean.1 h0 hh0).1 (hclean.1 h0 hh0).2 e rfl⟩
    simp only [transSeq, typeSubstSequent, List.mem_append, List.mem_map]
    exact Or.inr ⟨h0.instType Ty.var, ⟨h0, hh0, rfl⟩, rfl⟩

end TypeDefGate

end QEDFV.HOL
