import QEDFV.Signature.GlobalLocalState
import QEDFV.Signature.ScopedStack
import QEDFV.Extension.DefOK

namespace QEDFV

def audit_c5_def_head_monotonicity : Prop :=
  forall t c x, x ∈ DefHeads t -> x ∈ DefHeads (commitDefHead t c)

theorem audit_c5_def_head_monotonicity_proved : audit_c5_def_head_monotonicity := by
  intro t c x hx
  exact defheads_monotone_commit t c x hx

def audit_c6_pop_redefine_rejection : Prop :=
  forall s c ty s', c ∈ Reserved -> pop? (push s) = some s' -> add? s' c ty = none

theorem audit_c6_pop_redefine_rejection_proved : audit_c6_pop_redefine_rejection := by
  intro s c ty s' hReserved hPop
  cases hs : s.frames with
  | nil =>
      simp [push, pop?, hs] at hPop
  | cons f rest =>
      simp [push, pop?, hs] at hPop
      cases hPop
      unfold add?
      simp [hReserved]

def audit_c7_cycle_rejection : Prop :=
  forall t d, ¬ acyclic d.rhs d.c -> ¬ DefOK t d

theorem audit_c7_cycle_rejection_proved : audit_c7_cycle_rejection := by
  intro t d hCycle hDef
  rcases hDef with ⟨_, _, _, _, hAcyclic, _⟩
  exact hCycle hAcyclic

end QEDFV
