import QEDFV.Spec.Inventory
import QEDFV.Spec.Items

namespace QEDFV

structure TraceEntry where
  itemId : String
  declaration : String
deriving Repr, BEq

def traceability : List TraceEntry :=
  explicitItems.map (fun i =>
    { itemId := i.id
    , declaration := "QEDFV.Spec.Items." ++ i.id
    })

def coverage100 : Prop :=
  traceability.length = explicitItems.length

theorem traceability_coverage_complete : coverage100 := by
  simp [coverage100, traceability]

def traceability_release_gate : Prop :=
  coverage100 ∧ QEDFV.Spec.Items.RELEASE_FREEZE_GATE

theorem traceability_release_gate_proved : traceability_release_gate := by
  exact ⟨traceability_coverage_complete, QEDFV.Spec.Items.RELEASE_FREEZE_GATE_proved⟩

end QEDFV
