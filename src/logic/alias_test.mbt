///|
/// Blackbox test package: full `using` union (main `alias.mbt` is not in scope here).
using @kernel {
  type KernelState,
  type Term,
  type Thm,
  type HolType,
  type SigError,
  type LogicError,
  type ExtensionCert,
  empty_kernel_state,
  bool_ty,
  fun_ty,
  mk_tyvar,
  ty_eq,
  ks_add_const,
  ks_lookup_const,
  ks_definition_theorem,
  ks_mk_const,
  ks_define_const_thm,
  ks_push_scope,
  mk_comb,
  mk_abs,
  mk_const,
  mk_var,
  mk_eq,
  dest_comb,
  dest_abs,
  dest_const,
  dest_eq,
  term_alpha_eq,
  term_logical_eq,
  thm_concl,
  thm_hyps,
  thm_hyp_count,
  type_of,
  assume_checked,
  add_assum_checked,
  refl_checked,
  trans_checked,
  mk_comb_rule_checked,
  abs_rule_checked,
  beta_rule_checked,
  eq_mp_checked,
  deduct_antisym_rule_checked,
  inst_type,
  inst_checked,
  ks_register_type_definition,
  ks_specify_const,
  ks_register_ind_infinity_axiom,
  ks_ind_infinity_axiom,
  ks_typedef_contract,
  ks_extension_cert_count,
  ks_extension_cert_at,
  ks_conservative_replay_ok,
  ind_ty,
}

///|
using @logic {
  type PropApplyTheoremResolution,
  type PropExactTheoremResolution,
  type PropExactWitness,
  type PropExactWitnessResolution,
  type PropTheoremClass,
  type PropTheoremEntry,
  type PropRefResolution,
  logic_prop_theorem_count,
  logic_prop_theorem_at,
  logic_prop_theorem_entry,
  logic_prop_named_theorem,
  logic_prop_context_theorem,
  logic_prop_context_apply_theorem,
  logic_prop_resolve_apply_theorem,
  logic_prop_resolve_exact_theorem,
  logic_prop_resolve_exact_witness,
  logic_prop_resolve_ref,
}

///|
test "alias keepalive for logic imports" {
  let _ : SigError? = None
  let _ : LogicError? = None
  let _ : ExtensionCert? = None
  let _ = ty_eq
  let _ = ks_definition_theorem
  let _ = ks_define_const_thm
  let _ = dest_comb
  let _ = dest_abs
  let _ = dest_const
  let _ = assume_checked
  let _ = add_assum_checked
  let _ = refl_checked
  let _ = trans_checked
  let _ = mk_comb_rule_checked
  let _ = abs_rule_checked
  let _ = beta_rule_checked
  let _ = eq_mp_checked
  let _ = deduct_antisym_rule_checked
  let _ = inst_type
  let _ = inst_checked
  let _ = ks_register_type_definition
  let _ = ks_specify_const
  let _ = ks_register_ind_infinity_axiom
  let _ = ks_ind_infinity_axiom
  let _ = ks_typedef_contract
  let _ = ks_extension_cert_count
  let _ = ks_extension_cert_at
  let _ = ks_conservative_replay_ok
  let _ = logic_prop_theorem_count
  let _ = logic_prop_theorem_at
  let _ = logic_prop_theorem_entry
  let _ = logic_prop_named_theorem
  let _ = logic_prop_context_theorem
  let _ = logic_prop_context_apply_theorem
  let _ = logic_prop_resolve_apply_theorem
  let _ = logic_prop_resolve_exact_theorem
  let _ = logic_prop_resolve_exact_witness
  let _ = logic_prop_resolve_ref
  let _ : PropApplyTheoremResolution? = None
  let _ : PropExactTheoremResolution? = None
  let _ : PropExactWitness? = None
  let _ : PropExactWitnessResolution? = None
  let _ : PropTheoremClass? = None
  let _ : PropTheoremEntry? = None
  let _ : PropRefResolution? = None
}
