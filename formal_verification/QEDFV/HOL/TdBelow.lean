import QEDFV.HOL.TdMain
import QEDFV.HOL.UnfoldBelow

/-! Syntactic conservativity of a parameter-free type definition above older definitions and
specifications, which may be polymorphic: the older steps are unfolded one by one, from the
step directly below the type definition, until the history is empty. -/
namespace QEDFV.HOL

variable {S : Signature}

theorem TypeDefGate.Ok.unfold {G : TypeDefGate S} (h : G.Ok) (U : Unfolder S) (hB : U.Below G) :
    (G.unfold U hB).Ok where
  closed := h.closed
  pred_ground := by
    have := Term.annotVars_replConst_subset U.R U.annot G.pred
    rw [h.pred_ground] at this
    exact Set.subset_eq_empty this rfl

/-- Unfold a list of declarations in a sequent, the step directly below the type definition
first. -/
def Sequent.unfoldAll {Γ : List Ty} (us : List (Unfolder S)) (s : Sequent S Γ) : Sequent S Γ :=
  us.foldl (fun s U ↦ s.replConst U.R) s

theorem Sequent.clean_replConst {Γ : List Ty} {k : Nat} {s : Sequent S Γ} (U : Unfolder S)
    (hk : k ∉ U.T0) (h : s.Clean k) : (s.replConst U.R).Clean k := by
  have hsub := Sequent.tyCons_replConst_subset U.R U.T0 U.tyC s
  have hS : k ∉ s.tyCons := fun hm ↦ by
    rcases hm with ⟨x, hx, hxk⟩ | hxk
    · exact h.1 x hx hxk
    · exact h.2 hxk
  refine ⟨fun x hx hxk ↦ ?_, fun hxk ↦ ?_⟩
  · rcases hsub (Sequent.tyCons_hyp hx hxk) with h' | h'
    · exact hS h'
    · exact hk h'
  · rcases hsub (Sequent.tyCons_concl _ hxk) with h' | h'
    · exact hS h'
    · exact hk h'

/-- **Conservativity of a parameter-free type definition above older declarations.** A
sequent whose types avoid the new constructor, derivable after the type definition above the
declarations `us`, has its unfolding derivable at the empty history, given a witness for the
predicate at the old history. The declarations may be polymorphic. -/
theorem TypeDefGate.typedef_conservative_unfold (us : List (Unfolder S)) :
    ∀ (G : TypeDefGate S) (hOk : G.Ok) (hB : ∀ U, U ∈ us → U.Below G) {Γ : List Ty}
      {s : Sequent S Γ} (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) (hclean : s.Clean G.k)
      {w : Term S [] G.repTy}
      (hwit : HistoryDerivation S (us.map Unfolder.step) { hyps := [], concl := G.pred.app w })
      (d : HistoryDerivation S (ModelExtension.typeDefinition G :: us.map Unfolder.step) s),
      HistoryDerivation S ([] : List (ModelExtension S)) (s.unfoldAll us) := by
  induction us with
  | nil =>
      intro G hOk hB Γ s hΓ hclean w hwit d
      exact G.typedef_conservative hOk hΓ hclean hwit d
  | cons U us ih =>
      intro G hOk hB Γ s hΓ hclean w hwit d
      have hBU : U.Below G := hB U (List.mem_cons_self ..)
      have d' := HistoryDerivation.erase_below G U hBU d
      have hw' : HistoryDerivation S (us.map Unfolder.step)
          { hyps := [], concl := (G.unfold U hBU).pred.app (w.replConst U.R) } :=
        U.erase hwit
      exact ih (G.unfold U hBU) (hOk.unfold U hBU)
        (fun U' hU' ↦ ⟨(hB U' (List.mem_cons_of_mem _ hU')).k_fresh,
          (hB U' (List.mem_cons_of_mem _ hU')).rep_fresh,
          (hB U' (List.mem_cons_of_mem _ hU')).abs_fresh,
          (hB U' (List.mem_cons_of_mem _ hU')).id_ne_rep,
          (hB U' (List.mem_cons_of_mem _ hU')).id_ne_abs⟩)
        hΓ (Sequent.clean_replConst U hBU.k_fresh hclean) hw' d'

theorem Unfolder.fixes_seq (U : Unfolder S) {Γ : List Ty} (s : Sequent S Γ)
    (h : U.id ∉ s.constIds) : s.replConst U.R = s := by
  cases s with
  | mk hyps concl =>
      have hh : ∀ x ∈ hyps, U.id ∉ x.constIds := fun x hx hm ↦
        h (Sequent.mem_constIds_hyp (s := { hyps := hyps, concl := concl }) hx hm)
      have hc : U.id ∉ concl.constIds := fun hm ↦
        h (Sequent.mem_constIds_concl (s := { hyps := hyps, concl := concl }) hm)
      simp only [Sequent.replConst]
      rw [U.fixes concl hc]
      congr 1
      rw [List.map_congr_left (fun x hx ↦ U.fixes x (hh x hx))]
      simp

theorem Sequent.unfoldAll_of_not_mem {Γ : List Ty} (us : List (Unfolder S)) (s : Sequent S Γ)
    (h : ∀ U, U ∈ us → U.id ∉ s.constIds) : s.unfoldAll us = s := by
  induction us with
  | nil => rfl
  | cons U us ih =>
      simp only [Sequent.unfoldAll, List.foldl_cons]
      rw [U.fixes_seq s (h U (List.mem_cons_self ..))]
      exact ih (fun U' hU' ↦ h U' (List.mem_cons_of_mem _ hU'))

/-- A sequent in the language of neither the type definition nor the older declarations is
derivable at the empty history. -/
theorem TypeDefGate.typedef_conservative_old (us : List (Unfolder S)) (G : TypeDefGate S)
    (hOk : G.Ok) (hB : ∀ U, U ∈ us → U.Below G) {Γ : List Ty} {s : Sequent S Γ}
    (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) (hclean : s.Clean G.k)
    (hold : ∀ U, U ∈ us → U.id ∉ s.constIds) {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S (us.map Unfolder.step) { hyps := [], concl := G.pred.app w })
    (d : HistoryDerivation S (ModelExtension.typeDefinition G :: us.map Unfolder.step) s) :
    HistoryDerivation S ([] : List (ModelExtension S)) s := by
  have := G.typedef_conservative_unfold us hOk hB hΓ hclean hwit d
  rwa [Sequent.unfoldAll_of_not_mem us s hold] at this

end QEDFV.HOL
