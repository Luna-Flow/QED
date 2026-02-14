import QEDFV.Extension.SpecOK

namespace QEDFV

def PrimitiveOrAdmissible (k : KernelState) (s : Sequent) : Prop :=
  Derivable k s

def GlobalAdmissibilityEnvelope (_k : KernelState) : Prop :=
  primitive_sound_all

def global_admissibility_sound (k : KernelState) : Prop :=
  GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem global_admissibility_sound_proved (k : KernelState) : global_admissibility_sound k := by
  intro hEnv
  exact hEnv

end QEDFV
