import QEDFV.HOL.Soundness
import QEDFV.HOL.HistoryAuditExamples
import QEDFV.HOL.DeclarationAllocation
import QEDFV.HOL.DeclarationAllocationExamples
import QEDFV.HOL.Unfold
import QEDFV.HOL.TdNorm
import QEDFV.HOL.TdMain
import QEDFV.HOL.ConnectiveExamples
import QEDFV.HOL.SpecErasure

/-! Reproducible foundation audit for the public Typed HOL core results. -/

#print axioms QEDFV.HOL.typed_hol_core_proof_complete
#print axioms QEDFV.HOL.derivation_sound
#print axioms QEDFV.HOL.derive_truth_and_truth
#print axioms QEDFV.HOL.derive_forall_refl
#print axioms QEDFV.HOL.derive_imp_self
#print axioms QEDFV.HOL.indInfinitySentence_valid
#print axioms QEDFV.HOL.valid_definition_equation
#print axioms QEDFV.HOL.typed_signature_generic_consistency
#print axioms QEDFV.HOL.typed_signature_generic_nonvalid_in_extension
#print axioms QEDFV.HOL.extension_derivation_sound
#print axioms QEDFV.HOL.typed_extension_derivation_sound
#print axioms QEDFV.HOL.history_derivation_sound
#print axioms QEDFV.HOL.typed_history_derivation_sound
#print axioms QEDFV.HOL.history_derivation_old_language_valid
#print axioms QEDFV.HOL.history_generic_false_not_derivable
#print axioms QEDFV.HOL.HistoryDerivation.erase_definition
#print axioms QEDFV.HOL.HistoryDerivation.definition_conservative
#print axioms QEDFV.HOL.TypeDefGate.nrm_range
#print axioms QEDFV.HOL.TypeDefGate.nrm_fix
#print axioms QEDFV.HOL.TypeDefGate.nrm_idem
#print axioms QEDFV.HOL.TypeDefGate.hd_trans
#print axioms QEDFV.HOL.TypeDefGate.typedef_conservative
#print axioms QEDFV.HOL.HistoryDerivation.erase_specification
#print axioms QEDFV.HOL.HistoryDerivation.specification_conservative
#print axioms QEDFV.HOL.unit_absRep_function_valid
#print axioms QEDFV.HOL.unit_history_composition_nonvacuous
#print axioms QEDFV.HOL.falseGate_no_witness
#print axioms QEDFV.HOL.falseGate_witness_not_valid
#print axioms QEDFV.HOL.falseGate_witness_not_derivable
#print axioms QEDFV.HOL.unitGate_ids_in_history
#print axioms QEDFV.HOL.unitGate_not_fresh_after_introduction
#print axioms QEDFV.HOL.DeclTable.old_declares_after_add
#print axioms QEDFV.HOL.DeclTable.old_ids_subset_after_add
#print axioms QEDFV.HOL.DeclTable.compatible_add
#print axioms QEDFV.HOL.DeclTable.declared_type_unique
#print axioms QEDFV.HOL.DeclTable.add_allocation_compatible
#print axioms QEDFV.HOL.trueTable2_compatible
#print axioms QEDFV.HOL.trueTable2_rep_type_is_stable
#print axioms QEDFV.HOL.trueTable2_abs_type_is_stable
#print axioms QEDFV.HOL.Ty.carrier_nonempty
#print axioms QEDFV.HOL.Ty.denote_congr
#print axioms QEDFV.HOL.Ty.denote_congr_vars
#print axioms QEDFV.HOL.Ty.tyCons_subst
#print axioms QEDFV.HOL.Term.tyCons_instType
#print axioms QEDFV.HOL.Term.eval_congr
#print axioms QEDFV.HOL.Term.eval_congr_κ
#print axioms QEDFV.HOL.Term.eval_congr_vars
#print axioms QEDFV.HOL.valid_transport_κ
#print axioms QEDFV.HOL.valid_iff_κ
#print axioms QEDFV.HOL.valid_old_language_iff
#print axioms QEDFV.HOL.valid_definition_old_language_iff
#print axioms QEDFV.HOL.valid_allEq_one_unchanged
#print axioms QEDFV.HOL.valid_allEq_zero_changes
#print axioms QEDFV.HOL.TypeDefGate.newTyCon_isAdmissible
#print axioms QEDFV.HOL.TypeDefGate.valid_absRep
#print axioms QEDFV.HOL.TypeDefGate.valid_repRange
#print axioms QEDFV.HOL.TypeDefGate.valid_repAbs
#print axioms QEDFV.HOL.TypeDefGate.laws
#print axioms QEDFV.HOL.TypeDefGate.laws_of_witness_valid
#print axioms QEDFV.HOL.TypeDefGate.valid_iff_old
#print axioms QEDFV.HOL.TypeDefGate.valid_iff_old_canonical
#print axioms QEDFV.HOL.TypeDefGate.holdsAny_iff
#print axioms QEDFV.HOL.TypeDefGate.repVal_eq_val
#print axioms QEDFV.HOL.ModelExtension.valid_iff
#print axioms QEDFV.HOL.canonicalConstVal_local
#print axioms QEDFV.HOL.trueGate_laws
#print axioms QEDFV.HOL.falseGate_repRange_not_valid
#print axioms QEDFV.HOL.DefinitionGate.withDefinition_local
#print axioms QEDFV.HOL.SpecificationGate.withSpecification_local
#print axioms QEDFV.HOL.TypeDefGate.newConst_local
#print axioms QEDFV.HOL.TypeDefGate.valid_law
#print axioms QEDFV.HOL.ModelExtension.interpret_isLocal
#print axioms QEDFV.HOL.interpretModels_isLocal
#print axioms QEDFV.HOL.valid_interpretModels_iff
#print axioms QEDFV.HOL.typed_global_semantic_conservativity_models
#print axioms QEDFV.HOL.typed_extension_derivation_sound_default
#print axioms QEDFV.HOL.extension_derivation_old_language_valid
#print axioms QEDFV.HOL.typed_signature_generic_nonvalid_in_history
#print axioms QEDFV.HOL.unit_laws_valid
#print axioms QEDFV.HOL.unit_old_language_valid
#print axioms QEDFV.HOL.unit_model_nontrivial
