import QEDFV.Envelope.Admissibility
import QEDFV.Semantics.ModelClass
import QEDFV.Conservativity.GlobalConservativity

namespace QEDFV

def soundness_dependency_map_closed : Prop :=
  primitive_sound_all ∧
  (∀ k, GlobalAdmissibilityEnvelope k -> primitive_sound_all) ∧
  (∀ t, modelClassNonempty t -> modelClassNonempty t)

def kernel_soundness_target : Prop :=
  forall k, GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem kernel_soundness_bridge : kernel_soundness_target := by
  intro k hk
  exact global_admissibility_sound_proved k hk

theorem soundness_dependency_map_closed_proved : soundness_dependency_map_closed := by
  refine ⟨?_, ?_, ?_⟩
  · exact primitive_sound_all_proved
  · intro k hk
    exact global_admissibility_sound_proved k hk
  · intro t h
    exact h

def global_conservativity_target : Prop :=
  ∀ ks t0 steps d s,
    Derives ks d s ->
    OldLang t0 s ->
    Derives ks (eraseSequence steps d) s

theorem global_conservativity_target_proved : global_conservativity_target := by
  intro ks t0 steps d s hDerives hOld
  exact global_conservativity_finite_step ks t0 steps d s hDerives hOld

end QEDFV
