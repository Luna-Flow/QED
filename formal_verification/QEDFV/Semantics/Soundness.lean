import QEDFV.Envelope.Admissibility

namespace QEDFV

def soundness_dependency_map_closed : Prop :=
  primitive_sound_all

def kernel_soundness_target : Prop :=
  forall k, GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem kernel_soundness_bridge : kernel_soundness_target := by
  intro k hk
  exact global_admissibility_sound_proved k hk

end QEDFV
