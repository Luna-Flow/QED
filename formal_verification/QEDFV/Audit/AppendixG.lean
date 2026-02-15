import QEDFV.Engineering.Conformance

namespace QEDFV

def appendix_g_rule_fidelity_replay : Prop :=
  ∀ r : Realization, FaithfulRealization r -> ruleFidelity r

theorem appendix_g_rule_fidelity_replay_proved : appendix_g_rule_fidelity_replay := by
  intro r h
  exact h.rule

def appendix_g_boundary_fidelity : Prop :=
  ∀ r : Realization, FaithfulRealization r -> boundaryFidelity r

theorem appendix_g_boundary_fidelity_proved : appendix_g_boundary_fidelity := by
  intro r h
  exact h.boundary

def appendix_g_scope_fidelity : Prop :=
  ∀ r : Realization, FaithfulRealization r -> scopeFidelity r

theorem appendix_g_scope_fidelity_proved : appendix_g_scope_fidelity := by
  intro r h
  exact h.scope

def appendix_g_replay_trace_fidelity : Prop :=
  ∀ r : Realization, FaithfulRealization r -> replayTraceFidelity r

theorem appendix_g_replay_trace_fidelity_proved : appendix_g_replay_trace_fidelity := by
  intro r h
  exact h.trace

def appendix_g_gate_fidelity : Prop :=
  ∀ r : Realization, FaithfulRealization r -> gateFidelity r

theorem appendix_g_gate_fidelity_proved : appendix_g_gate_fidelity := by
  intro r h
  exact h.gate

def appendix_g_certificate_non_authority : Prop :=
  ∀ r : Realization, FaithfulRealization r -> certificateNonAuthority r

theorem appendix_g_certificate_non_authority_proved : appendix_g_certificate_non_authority := by
  intro r h
  exact h.cert

def appendix_g_transfer_trace_alignment : Prop :=
  ∀ r : Realization, ∀ s : Sequent,
    FaithfulRealization r ->
    r.accepts s ->
    ∃ k, Derivable k s ∧
      derivationPrimitiveInstances (r.replayDerivation s) = r.replayPrimitiveInstances s ∧
      primitiveInstanceNames (r.replayPrimitiveInstances s) = r.replayPrimitiveTrace s ∧
      primitiveInstanceTrace (r.replayPrimitiveInstances s)

theorem appendix_g_transfer_trace_alignment_proved : appendix_g_transfer_trace_alignment := by
  intro r s hFaithful hAccept
  exact implementation_to_logic_transfer_with_trace r hFaithful s hAccept

end QEDFV
