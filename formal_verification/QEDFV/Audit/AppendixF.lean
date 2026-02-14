import QEDFV.Extension.SpecOK

namespace QEDFV

def audit_f1_empty_hypothesis_witness_required : Prop :=
  forall t s, SpecOK t s -> witnessShape s

theorem audit_f1_empty_hypothesis_witness_required_proved : audit_f1_empty_hypothesis_witness_required := by
  intro t s hSpec
  rcases hSpec with ⟨_, _, hWitness, _, _, _, _⟩
  exact hWitness

def audit_f2_freshness_collision : Prop :=
  forall t s, SpecOK t s -> (s.c ∉ DefHeads t ∧ s.c ∉ Reserved)

theorem audit_f2_freshness_collision_proved : audit_f2_freshness_collision := by
  intro t s hSpec
  rcases hSpec with ⟨hDef, hRes, _, _, _, _, _⟩
  exact ⟨hDef, hRes⟩

def audit_f3_type_schema_widening_rejected : Prop :=
  forall t s, SpecOK t s -> noImplicitWidening s

theorem audit_f3_type_schema_widening_rejected_proved : audit_f3_type_schema_widening_rejected := by
  intro t s hSpec
  rcases hSpec with ⟨_, _, _, _, _, _, hNoWidening⟩
  exact hNoWidening

def audit_f4_derived_path_integrity : Prop :=
  forall t s, spec_derived_path_obligation t s

theorem audit_f4_derived_path_integrity_proved : audit_f4_derived_path_integrity := by
  intro t s
  exact spec_derived_path_obligation_proved t s

def audit_f5_old_language_conservativity : Prop :=
  forall t s, SpecOK t s -> spec_extension_conservative t s

theorem audit_f5_old_language_conservativity_proved : audit_f5_old_language_conservativity := by
  intro t s hSpec
  exact spec_extension_conservative_proved t s

end QEDFV
