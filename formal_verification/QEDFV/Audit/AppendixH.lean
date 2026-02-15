import QEDFV.Audit.AppendixG

namespace QEDFV

structure ClaimTraceEntry where
  claimId : String
  definitionAnchor : String
  theoremAnchor : String
deriving Repr, BEq

def appendix_h_claim_trace_matrix : List ClaimTraceEntry :=
  [ { claimId := "C1_RULE_SOUNDNESS", definitionAnchor := "QEDFV.primitive_sound_all", theoremAnchor := "QEDFV.primitive_sound_all_proved" }
  , { claimId := "C2_DEF_CONSERVATIVITY", definitionAnchor := "QEDFV.DefOK", theoremAnchor := "QEDFV.def_extension_conservative" }
  , { claimId := "C3_TYPE_CONSERVATIVITY", definitionAnchor := "QEDFV.TypeDefOK", theoremAnchor := "QEDFV.SEC6_TYPEDEF_OK_proved" }
  , { claimId := "C4_SPEC_CONSERVATIVITY", definitionAnchor := "QEDFV.SpecOK", theoremAnchor := "QEDFV.spec_extension_conservative_proved" }
  , { claimId := "C5_SCOPE_STABILITY", definitionAnchor := "QEDFV.ScopeMutation", theoremAnchor := "QEDFV.resolved_theorem_stability_under_scope_mutation" }
  , { claimId := "C6_BOUNDARY_STABILITY", definitionAnchor := "QEDFV.BoundaryLaws", theoremAnchor := "QEDFV.SEC9_RULE_LIFT_SAFETY_proved" }
  , { claimId := "C7_GLOBAL_CONSERVATIVITY", definitionAnchor := "QEDFV.eraseSequence", theoremAnchor := "QEDFV.global_conservativity_finite_step" }
  , { claimId := "C8_CONFORMANCE_TRANSFER", definitionAnchor := "QEDFV.FaithfulRealization", theoremAnchor := "QEDFV.implementation_to_logic_transfer" }
  , { claimId := "C9_NON_TRIVIALITY", definitionAnchor := "QEDFV.AdmissibleModelClass", theoremAnchor := "QEDFV.semantic_non_triviality_transfer" }
  , { claimId := "C10_CERT_NON_AUTHORITY", definitionAnchor := "QEDFV.certificateNonAuthority", theoremAnchor := "QEDFV.appendix_g_certificate_non_authority_proved" }
  , { claimId := "C11_REPLAY_TRACE_TIGHTENING", definitionAnchor := "QEDFV.replayTraceFidelity", theoremAnchor := "QEDFV.appendix_g_replay_trace_fidelity_proved" }
  ]

def appendix_h_matrix_complete : Prop :=
  appendix_h_claim_trace_matrix.length = 11

theorem appendix_h_matrix_complete_proved : appendix_h_matrix_complete := by
  unfold appendix_h_matrix_complete appendix_h_claim_trace_matrix
  decide

end QEDFV
