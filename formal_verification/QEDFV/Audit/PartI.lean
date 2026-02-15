import QEDFV.Spec.Items
import QEDFV.Spec.Traceability

namespace QEDFV

structure PartIVerification where
  constPrincipalSchema : QEDFV.Spec.Items.SEC4_CONST_PRINCIPAL_SCHEMA
  typeInstanceRelation : QEDFV.Spec.Items.SEC4_TYPE_INSTANCE_REL
  rconstInstanceTyping : QEDFV.Spec.Items.SEC7_RCONST_INSTANCE_TYPING
  polyConstInstantiation : QEDFV.Spec.Items.SEC7_POLY_CONST_INST_ADMISSIBLE
  noMonomorphicLockout : QEDFV.Spec.Items.SEC7_NO_MONO_LOCKOUT
  typedefGate : QEDFV.Spec.Items.SEC6_TYPEDEF_OK
  typedefContractSurj : QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_ABS_SURJ
  typedefContractRange : QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_REP_RANGE
  typedefContractRetract : QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_REP_ABS
  nonemptyPreservation : QEDFV.Spec.Items.SEC6_TYPE_NONEMPTY_PRESERVE
  alphaQuotientAssumptions : QEDFV.Spec.Items.SEC10_ALPHA_QUOTIENT_ASSUMPTIONS
  alphaUnionIdempotent : QEDFV.Spec.Items.SEC10_ALPHA_SET_IDEMPOTENCE
  alphaUnionComm : QEDFV.Spec.Items.SEC10_ALPHA_SET_COMM
  alphaRemoveCompat : QEDFV.Spec.Items.SEC10_ALPHA_REMOVE_COMPAT
  instTypeRule : QEDFV.Spec.Items.SEC14_RULE_INST_TYPE
  instTypeValidSubst : QEDFV.Spec.Items.SEC14_INST_TYPE_VALID_SUBST
  instTypeAdmissibleImage : QEDFV.Spec.Items.SEC14_INST_TYPE_ADMISSIBLE_IMAGE
  instTypeTypingPreserve : QEDFV.Spec.Items.SEC14_INST_TYPE_TYPING_PRESERVE
  instTypeDefCoherent : QEDFV.Spec.Items.SEC14_INST_TYPE_DEF_COHERENT
  instTypeConstInstance : QEDFV.Spec.Items.SEC14_INST_TYPE_CONST_INSTANCE_OK
  instTypeStructure : QEDFV.Spec.Items.SEC14_INST_TYPE_STRUCTURE
  instRule : QEDFV.Spec.Items.SEC14_RULE_INST
  derivationObject : QEDFV.Spec.Items.SEC15_DERIVATION_OBJECT
  eraseDef : QEDFV.Spec.Items.SEC15_ERASE_DEF
  eraseSpec : QEDFV.Spec.Items.SEC15_ERASE_SPEC
  eraseTypeDef : QEDFV.Spec.Items.SEC15_ERASE_TYPEDEF
  globalConservativity : QEDFV.Spec.Items.SEC15_GLOBAL_CONSERVATIVITY_FINITE
  soundnessStrategy : QEDFV.Spec.Items.SEC15_SOUNDNESS_STRATEGY

def partI_semantic_alignment : Prop :=
  Nonempty PartIVerification

theorem partI_semantic_alignment_proved : partI_semantic_alignment := by
  refine ⟨{
    constPrincipalSchema := QEDFV.Spec.Items.SEC4_CONST_PRINCIPAL_SCHEMA_proved
    typeInstanceRelation := QEDFV.Spec.Items.SEC4_TYPE_INSTANCE_REL_proved
    rconstInstanceTyping := QEDFV.Spec.Items.SEC7_RCONST_INSTANCE_TYPING_proved
    polyConstInstantiation := QEDFV.Spec.Items.SEC7_POLY_CONST_INST_ADMISSIBLE_proved
    noMonomorphicLockout := QEDFV.Spec.Items.SEC7_NO_MONO_LOCKOUT_proved
    typedefGate := QEDFV.Spec.Items.SEC6_TYPEDEF_OK_proved
    typedefContractSurj := QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_ABS_SURJ_proved
    typedefContractRange := QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_REP_RANGE_proved
    typedefContractRetract := QEDFV.Spec.Items.SEC6_TYPEDEF_PRODUCT_REP_ABS_proved
    nonemptyPreservation := QEDFV.Spec.Items.SEC6_TYPE_NONEMPTY_PRESERVE_proved
    alphaQuotientAssumptions := QEDFV.Spec.Items.SEC10_ALPHA_QUOTIENT_ASSUMPTIONS_proved
    alphaUnionIdempotent := QEDFV.Spec.Items.SEC10_ALPHA_SET_IDEMPOTENCE_proved
    alphaUnionComm := QEDFV.Spec.Items.SEC10_ALPHA_SET_COMM_proved
    alphaRemoveCompat := QEDFV.Spec.Items.SEC10_ALPHA_REMOVE_COMPAT_proved
    instTypeRule := QEDFV.Spec.Items.SEC14_RULE_INST_TYPE_proved
    instTypeValidSubst := QEDFV.Spec.Items.SEC14_INST_TYPE_VALID_SUBST_proved
    instTypeAdmissibleImage := QEDFV.Spec.Items.SEC14_INST_TYPE_ADMISSIBLE_IMAGE_proved
    instTypeTypingPreserve := QEDFV.Spec.Items.SEC14_INST_TYPE_TYPING_PRESERVE_proved
    instTypeDefCoherent := QEDFV.Spec.Items.SEC14_INST_TYPE_DEF_COHERENT_proved
    instTypeConstInstance := QEDFV.Spec.Items.SEC14_INST_TYPE_CONST_INSTANCE_OK_proved
    instTypeStructure := QEDFV.Spec.Items.SEC14_INST_TYPE_STRUCTURE_proved
    instRule := QEDFV.Spec.Items.SEC14_RULE_INST_proved
    derivationObject := QEDFV.Spec.Items.SEC15_DERIVATION_OBJECT_proved
    eraseDef := QEDFV.Spec.Items.SEC15_ERASE_DEF_proved
    eraseSpec := QEDFV.Spec.Items.SEC15_ERASE_SPEC_proved
    eraseTypeDef := QEDFV.Spec.Items.SEC15_ERASE_TYPEDEF_proved
    globalConservativity := QEDFV.Spec.Items.SEC15_GLOBAL_CONSERVATIVITY_FINITE_proved
    soundnessStrategy := QEDFV.Spec.Items.SEC15_SOUNDNESS_STRATEGY_proved
  }⟩

def partI_verification_complete : Prop :=
  partI_semantic_alignment ∧ QEDFV.coverage100

theorem partI_verification_complete_proved : partI_verification_complete := by
  exact ⟨partI_semantic_alignment_proved, QEDFV.traceability_coverage_complete⟩

end QEDFV
