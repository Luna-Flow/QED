import QEDFV.Extension.SpecOK

namespace QEDFV

def PrimitiveOrAdmissible (k : KernelState) (s : Sequent) : Prop :=
  Derivable k s

def TheoryStateWellFormed (t : TheoryState) : Prop :=
  ("bool", 0) ∈ t.tySymbols ∧
  ("fun", 2) ∈ t.tySymbols ∧
  ("ind", 0) ∈ t.tySymbols ∧
  (∀ c, c ∈ t.defHeads -> c ∈ t.committedConsts)

def GlobalAdmissibilityEnvelope (k : KernelState) : Prop :=
  ScopedWF k.S ∧ TheoryStateWellFormed k.T

def global_admissibility_sound (k : KernelState) : Prop :=
  GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem global_admissibility_sound_proved (k : KernelState) : global_admissibility_sound k := by
  intro _hEnv
  exact primitive_sound_all_proved

end QEDFV
