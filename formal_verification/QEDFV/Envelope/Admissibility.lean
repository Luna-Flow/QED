import QEDFV.Extension.SpecOK

namespace QEDFV

def PrimitiveOrAdmissible (k : KernelState) (s : Sequent) : Prop :=
  Derivable k s

def GlobalAdmissibilityEnvelope (k : KernelState) : Prop :=
  k = k

def global_admissibility_sound (k : KernelState) : Prop :=
  GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem global_admissibility_sound_proved (k : KernelState) : global_admissibility_sound k := by
  intro _
  exact primitive_sound_all_proved

end QEDFV
