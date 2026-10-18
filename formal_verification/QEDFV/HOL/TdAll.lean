import QEDFV.HOL.TdGood

/-! Conservativity of a parameter-free type definition above older parameter-free type
definitions, which in turn sit above any list of definitions and specifications. The older
declarations are unfolded in every type definition above them, from the top, and the result
is a derivation at a history of type definitions only. -/
namespace QEDFV.HOL

variable {S : Signature}

theorem mem_gatesUnfold' (U : Unfolder S) :
    ∀ (gs : List (TypeDefGate S)) (hB : ∀ G, G ∈ gs → U.Below G) (G' : TypeDefGate S),
      G' ∈ gatesUnfold U gs hB → ∃ (G0 : TypeDefGate S) (hG0 : G0 ∈ gs), G' = G0.unfold U (hB G0 hG0)
  | [], _, G', h => by simp [gatesUnfold] at h
  | G :: gs, hB, G', h => by
      simp only [gatesUnfold, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨G, List.mem_cons_self .., rfl⟩
      · obtain ⟨G0, hG0, hk⟩ :=
          mem_gatesUnfold' U gs (fun G' hG' ↦ hB G' (List.mem_cons_of_mem _ hG')) G' h
        exact ⟨G0, List.mem_cons_of_mem _ hG0, hk⟩

theorem Unfolder.Below.unfold {U U' : Unfolder S} {G : TypeDefGate S} (h : U'.Below G)
    (hU : U.Below G) : U'.Below (G.unfold U hU) :=
  ⟨h.k_fresh, h.rep_fresh, h.abs_fresh, h.id_ne_rep, h.id_ne_abs⟩

theorem TypeDefGate.Scoped.unfold {G G0 : TypeDefGate S} (U : Unfolder S) (hs : G.Scoped G0)
    (hG : U.Below G) (hG0 : U.Below G0) : (G.unfold U hG).Scoped (G0.unfold U hG0) where
  n_zero := hs.n_zero
  law := fun l ↦ by
    rw [show (l.sequent (G0.unfold U hG0)) = (l.sequent G0).replConst U.R from
      (G0.unfold_law U hG0 l).symm]
    exact G.unfold_oldLanguage U hG (hs.law l)
  newTy_free := hs.newTy_free
  repTy_free := hs.repTy_free

theorem Older.unfold {G G0 : TypeDefGate S} (U : Unfolder S) (hs : Older G G0)
    (hG : U.Below G) (hG0 : U.Below G0) : Older (G.unfold U hG) (G0.unfold U hG0) := fun l ↦ by
  rw [show (l.sequent (G0.unfold U hG0)) = (l.sequent G0).replConst U.R from
    (G0.unfold_law U hG0 l).symm]
  exact G.unfold_oldLanguage U hG (hs l)

theorem pairwise_gatesUnfold (U : Unfolder S) :
    ∀ (gs : List (TypeDefGate S)) (hB : ∀ G, G ∈ gs → U.Below G),
      List.Pairwise (Older (S := S)) gs → List.Pairwise (Older (S := S)) (gatesUnfold U gs hB)
  | [], _, _ => List.Pairwise.nil
  | G :: gs, hB, hp => by
      simp only [gatesUnfold]
      rw [List.pairwise_cons] at hp ⊢
      refine ⟨fun G' hG' ↦ ?_, pairwise_gatesUnfold U gs _ hp.2⟩
      obtain ⟨G0, hG0, rfl⟩ := mem_gatesUnfold' U gs _ G' hG'
      exact (hp.1 G0 hG0).unfold U _ _

/-- **Conservativity above older type definitions and declarations.** A parameter-free type
definition `G` above the older parameter-free type definitions `gs`, above the declarations
`us`, may be erased from a derivation of a sequent not using `G`'s type constructor: the
declarations are unfolded everywhere and the result is a derivation at a history of type
definitions. -/
theorem TypeDefGate.typedef_conservative_hist (us : List (Unfolder S)) :
    ∀ (G : TypeDefGate S) (gs : List (TypeDefGate S))
      (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0) (hpair : List.Pairwise (Older (S := S)) gs)
      (hB : ∀ U, U ∈ us → ∀ G', G' ∈ G :: gs → U.Below G') {Γ : List Ty} {s : Sequent S Γ}
      (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) (hclean : s.Clean G.k) {w : Term S [] G.repTy}
      (hwit : HistoryDerivation S (gs.map ModelExtension.typeDefinition ++ us.map Unfolder.step)
        { hyps := [], concl := G.pred.app w })
      (d : HistoryDerivation S (ModelExtension.typeDefinition G ::
        (gs.map ModelExtension.typeDefinition ++ us.map Unfolder.step)) s),
      ∃ gs' : List (TypeDefGate S),
        HistoryDerivation S (gs'.map ModelExtension.typeDefinition) (s.unfoldAll us) := by
  induction us with
  | nil =>
      intro G gs hsc hpair hB Γ s hΓ hclean w hwit d
      refine ⟨gs, ?_⟩
      have hw : HistoryDerivation S (gs.map ModelExtension.typeDefinition)
          { hyps := [], concl := G.pred.app w } := by simpa using hwit
      have d1 : HistoryDerivation S (ModelExtension.typeDefinition G ::
          gs.map ModelExtension.typeDefinition) s := by simpa using d
      obtain ⟨N, hI, hL⟩ := G.exists_oracle gs hsc hpair hw
      exact G.typedef_conservative_chain N gs hsc hpair hI hL hΓ hclean d1
  | cons U us ih =>
      intro G gs hsc hpair hB Γ s hΓ hclean w hwit d
      have hB' : ∀ G', G' ∈ G :: gs → U.Below G' := hB U (List.mem_cons_self ..)
      have hBG : U.Below G := hB' G (List.mem_cons_self ..)
      have hBgs : ∀ G', G' ∈ gs → U.Below G' := fun G' h ↦ hB' G' (List.mem_cons_of_mem _ h)
      have d' := HistoryDerivation.erase_chain U (G :: gs) hB' d
      have hw' := HistoryDerivation.erase_chain U gs hBgs hwit
      obtain ⟨gs', hgs'⟩ := ih (G.unfold U hBG) (gatesUnfold U gs hBgs)
        (fun G0' hG0' ↦ by
          obtain ⟨G0, hG0, rfl⟩ := mem_gatesUnfold' U gs hBgs G0' hG0'
          exact (hsc G0 hG0).unfold U hBG _)
        (pairwise_gatesUnfold U gs hBgs hpair)
        (fun U' hU' G' hG' ↦ by
          rcases List.mem_cons.1 hG' with rfl | hG'
          · exact (hB U' (List.mem_cons_of_mem _ hU') G (List.mem_cons_self ..)).unfold hBG
          · obtain ⟨G0, hG0, rfl⟩ := mem_gatesUnfold' U gs hBgs G' hG'
            exact (hB U' (List.mem_cons_of_mem _ hU') G0 (List.mem_cons_of_mem _ hG0)).unfold _)
        hΓ (Sequent.clean_replConst U hBG.k_fresh hclean) hw' d'
      exact ⟨gs', hgs'⟩

end QEDFV.HOL
