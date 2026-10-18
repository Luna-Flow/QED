import QEDFV.HOL.UnfoldBelow

/-! Unfolding a declaration below a chain of type definitions. -/
namespace QEDFV.HOL

variable {S : Signature}

/-- The gates of a chain with `U` unfolded in each predicate. -/
noncomputable def gatesUnfold (U : Unfolder S) :
    (gs : List (TypeDefGate S)) → (∀ G, G ∈ gs → U.Below G) → List (TypeDefGate S)
  | [], _ => []
  | G :: gs, h =>
      G.unfold U (h G (List.mem_cons_self ..)) ::
        gatesUnfold U gs (fun G' hG' ↦ h G' (List.mem_cons_of_mem _ hG'))

/-- The chain of type definitions with `U` unfolded in each predicate. -/
noncomputable def chainUnfold (U : Unfolder S) (gs : List (TypeDefGate S))
    (h : ∀ G, G ∈ gs → U.Below G) : List (ModelExtension S) :=
  (gatesUnfold U gs h).map ModelExtension.typeDefinition

@[simp] theorem chainUnfold_nil (U : Unfolder S) (h : ∀ G, G ∈ ([] : List (TypeDefGate S)) → U.Below G) :
    chainUnfold U [] h = [] := rfl

theorem chainUnfold_cons (U : Unfolder S) (G : TypeDefGate S) (gs : List (TypeDefGate S))
    (h : ∀ G', G' ∈ G :: gs → U.Below G') :
    chainUnfold U (G :: gs) h = ModelExtension.typeDefinition (G.unfold U (h G (List.mem_cons_self ..))) ::
      chainUnfold U gs (fun G' hG' ↦ h G' (List.mem_cons_of_mem _ hG')) := rfl

theorem chainUnfold_ids (U : Unfolder S) (es0 : List (ModelExtension S)) :
    ∀ (gs : List (TypeDefGate S)) (hB : ∀ G, G ∈ gs → U.Below G) (n : Nat),
      n ∈ modelHistoryIds (chainUnfold U gs hB ++ es0) →
      n ∈ modelHistoryIds (gs.map ModelExtension.typeDefinition ++ U.step :: es0) := by
  intro gs
  induction gs with
  | nil =>
      intro hB n hn
      simp only [chainUnfold_nil, List.nil_append, List.map_nil, modelHistoryIds, List.foldr_cons,
        Finset.mem_union] at hn ⊢
      exact Or.inr hn
  | cons G gs ih =>
      intro hB n hn
      simp only [chainUnfold_cons, List.cons_append, List.map_cons, modelHistoryIds, List.foldr_cons,
        Finset.mem_union, ModelExtension.constantIds] at hn ⊢
      rcases hn with hn | hn
      · exact Or.inl hn
      · exact Or.inr (ih _ n hn)

theorem chainUnfold_tyCons (U : Unfolder S) (es0 : List (ModelExtension S)) :
    ∀ (gs : List (TypeDefGate S)) (hB : ∀ G, G ∈ gs → U.Below G) (k : Nat),
      k ∈ modelHistoryTyCons (chainUnfold U gs hB ++ es0) →
      k ∈ modelHistoryTyCons (gs.map ModelExtension.typeDefinition ++ U.step :: es0) := by
  intro gs
  induction gs with
  | nil =>
      intro hB k hk
      obtain ⟨e, he, hke⟩ := hk
      simp only [chainUnfold_nil, List.nil_append] at he
      exact ⟨e, List.mem_cons_of_mem _ he, hke⟩
  | cons G gs ih =>
      intro hB k hk
      obtain ⟨e, he, hke⟩ := hk
      simp only [chainUnfold_cons, List.cons_append, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨ModelExtension.typeDefinition G, by simp, hke⟩
      · obtain ⟨e', he', hke'⟩ := ih (fun G' hG' ↦ hB G' (List.mem_cons_of_mem _ hG')) k ⟨e, he, hke⟩
        exact ⟨e', by simp only [List.map_cons, List.cons_append]; exact List.mem_cons_of_mem _ he', hke'⟩

theorem ExtensionDerivation.erase_chain_aux (G : TypeDefGate S) (U : Unfolder S)
    (hBG : U.Below G) (gs : List (TypeDefGate S)) (hB' : ∀ G', G' ∈ gs → U.Below G')
    (es0 : List (ModelExtension S))
    (hTail : ∀ {Γ : List Ty} {s : Sequent S Γ},
      HistoryDerivation S (gs.map ModelExtension.typeDefinition ++ U.step :: es0) s →
      HistoryDerivation S (chainUnfold U gs hB' ++ es0) (s.replConst U.R))
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) :
    h = ModelExtension.typeDefinition G ::
        (gs.map ModelExtension.typeDefinition ++ U.step :: es0) →
      HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hBG) ::
        (chainUnfold U gs hB' ++ es0)) (s.replConst U.R) := by
  induction d with
  | core d => exact fun _ ↦ Derivation.replConst U.R U.compat _ d
  | weaken e d hOld ih =>
      intro heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact .weaken _ (hTail (.extension d)) (G.unfold_oldLanguage U hBG hOld)
  | definition D' hFresh => intro heq; cases heq
  | specification E hFresh d ih => intro heq; cases heq
  | typedef G' l hk hrep habs w d ih =>
      intro heq
      obtain ⟨hG, rfl⟩ := List.cons.inj heq
      cases hG
      rw [G.unfold_law U hBG l]
      exact .typedef (G.unfold U hBG) l
        (fun hk' ↦ hk (chainUnfold_tyCons U es0 gs hB' _ hk'))
        (fun hn ↦ hrep (chainUnfold_ids U es0 gs hB' _ hn))
        (fun hn ↦ habs (chainUnfold_ids U es0 gs hB' _ hn))
        (w.replConst U.R) (hTail (.extension d))

theorem HistoryDerivation.erase_chain_aux (G : TypeDefGate S) (U : Unfolder S)
    (hBG : U.Below G) (gs : List (TypeDefGate S)) (hB' : ∀ G', G' ∈ gs → U.Below G')
    (es0 : List (ModelExtension S))
    (hTail : ∀ {Γ : List Ty} {s : Sequent S Γ},
      HistoryDerivation S (gs.map ModelExtension.typeDefinition ++ U.step :: es0) s →
      HistoryDerivation S (chainUnfold U gs hB' ++ es0) (s.replConst U.R))
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) :
    h = ModelExtension.typeDefinition G ::
        (gs.map ModelExtension.typeDefinition ++ U.step :: es0) →
      HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hBG) ::
        (chainUnfold U gs hB' ++ es0)) (s.replConst U.R) := by
  induction d with
  | core d => exact fun _ ↦ Derivation.replConst U.R U.compat _ d
  | extension d => exact fun heq ↦ ExtensionDerivation.erase_chain_aux G U hBG gs hB' es0 hTail d heq
  | weaken e d hOld ih =>
      intro heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact .weaken _ (hTail d) (G.unfold_oldLanguage U hBG hOld)
  | definition D' hFresh => intro heq; cases heq
  | specification E hFresh d ih => intro heq; cases heq
  | typedef G' l hk hrep habs w d ih =>
      intro heq
      obtain ⟨hG, rfl⟩ := List.cons.inj heq
      cases hG
      rw [G.unfold_law U hBG l]
      exact .typedef (G.unfold U hBG) l
        (fun hk' ↦ hk (chainUnfold_tyCons U es0 gs hB' _ hk'))
        (fun hn ↦ hrep (chainUnfold_ids U es0 gs hB' _ hn))
        (fun hn ↦ habs (chainUnfold_ids U es0 gs hB' _ hn))
        (w.replConst U.R) (hTail d)
  | addAssum p d ih => exact fun heq ↦ replConst_step_addAssum U.R p (ih heq)
  | weakenHyps L hL d ih => exact fun heq ↦ replConst_step_weakenHyps U.R L hL (ih heq)
  | trans hA hB dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_trans U.R hA hB (ihA heq) (ihB heq)
  | mkComb hA hB dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_mkComb U.R hA hB (ihA heq) (ihB heq)
  | abs d ih => exact fun heq ↦ replConst_step_abs U.R (ih heq)
  | eqMp hA hB dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_eqMp U.R hA hB (ihA heq) (ihB heq)
  | deduct dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_deduct U.R (ihA heq) (ihB heq)
  | instType θ d ih =>
      exact fun heq ↦ replConst_step_instType U.R U.compat θ (ih heq)
  | instTerm σ d ih => exact fun heq ↦ replConst_step_instTerm U.R σ (ih heq)
  | chooseWitness p w d ih =>
      exact fun heq ↦ replConst_step_chooseWitness U.R p w (ih heq)
  | truthIntro => exact fun heq ↦ HistoryDerivation.of_eq rfl .truthIntro
  | falsityElim q hA d ih => exact fun heq ↦ replConst_step_falsityElim U.R q hA (ih heq)
  | conjIntro hA hB dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_conjIntro U.R hA hB (ihA heq) (ihB heq)
  | conjElimLeft hA d ih => exact fun heq ↦ replConst_step_conjElimLeft U.R hA (ih heq)
  | conjElimRight hA d ih => exact fun heq ↦ replConst_step_conjElimRight U.R hA (ih heq)
  | impIntro p d ih => exact fun heq ↦ replConst_step_impIntro U.R p (ih heq)
  | impElim hA hB dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_impElim U.R hA hB (ihA heq) (ihB heq)
  | allIntro d ih => exact fun heq ↦ replConst_step_allIntro U.R (ih heq)
  | allElim t hA d ih => exact fun heq ↦ replConst_step_allElim U.R t hA (ih heq)
  | exIntro t hA d ih => exact fun heq ↦ replConst_step_exIntro U.R t hA (ih heq)
  | exElim hA dA dB ihA ihB =>
      exact fun heq ↦ replConst_step_exElim U.R hA (ihA heq) (ihB heq)
  | classical hA d ih => exact fun heq ↦ replConst_step_classical U.R hA (ih heq)
  | chooseHyp p w hA d ih => exact fun heq ↦ replConst_step_chooseHyp U.R p w hA (ih heq)

/-- **Erasing a declaration below a chain of type definitions.** -/
theorem HistoryDerivation.erase_chain (U : Unfolder S) :
    ∀ (gs : List (TypeDefGate S)) (hB : ∀ G, G ∈ gs → U.Below G)
      {es0 : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
      (d : HistoryDerivation S (gs.map ModelExtension.typeDefinition ++ U.step :: es0) s),
      HistoryDerivation S (chainUnfold U gs hB ++ es0) (s.replConst U.R) := by
  intro gs
  induction gs with
  | nil => intro hB es0 Γ s d; exact U.erase d
  | cons G gs ih =>
      intro hB es0 Γ s d
      exact HistoryDerivation.erase_chain_aux G U (hB G (List.mem_cons_self ..)) gs
        (fun G' hG' ↦ hB G' (List.mem_cons_of_mem _ hG')) es0
        (fun {Γ s} d' ↦ ih (fun G' hG' ↦ hB G' (List.mem_cons_of_mem _ hG')) d') d rfl

end QEDFV.HOL
