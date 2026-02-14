import QEDFV.Signature.TypeDef

namespace QEDFV

def audit_d1_type_witness_validity : Prop :=
  forall t k a repTy p w,
    TypeDefOK t k a repTy p w ->
    w.repName ∉ Reserved ∧ w.absName ∉ Reserved

theorem audit_d1_type_witness_validity_proved : audit_d1_type_witness_validity := by
  intro t k a repTy p w h
  rcases h with ⟨_, hRepReserved, hAbsReserved, _, _, _, _⟩
  exact ⟨hRepReserved, hAbsReserved⟩

def audit_d5_schema_instance_guard : Prop :=
  forall t k a repTy p w, TypeDefOK t k a repTy p w -> termTyvarsSubset p repTy

theorem audit_d5_schema_instance_guard_proved : audit_d5_schema_instance_guard := by
  intro t k a repTy p w h
  rcases h with ⟨_, _, _, _, _, _, hSubset⟩
  exact hSubset

def audit_d6_witness_const_id_drift : Prop :=
  forall t k a repTy p w,
    TypeDefOK t k a repTy p w -> (w.repName ∉ DefHeads t ∧ w.absName ∉ DefHeads t)

theorem audit_d6_witness_const_id_drift_proved : audit_d6_witness_const_id_drift := by
  intro t k a repTy p w h
  rcases h with ⟨_, _, _, hRep, hAbs, _, _⟩
  exact ⟨hRep, hAbs⟩

end QEDFV
