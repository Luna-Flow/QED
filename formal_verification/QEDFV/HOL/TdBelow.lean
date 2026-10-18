import QEDFV.HOL.TdMain
import QEDFV.HOL.UnfoldBelow

/-! Syntactic conservativity of a parameter-free type definition above older definitions and
specifications, which may be polymorphic: the older steps are unfolded one by one, from the
step directly below the type definition, until the history is empty. -/
namespace QEDFV.HOL

variable {S : Signature}

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

end QEDFV.HOL
