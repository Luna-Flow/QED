///| Blackbox test package: duplicate package-local `using` from `alias.mbt` plus

///|
/// test-only imports (`alias.mbt` is not in scope for blackbox tests).
using @kernel {
  type KernelState,
  type Term,
  empty_kernel_state,
  bool_ty,
  ks_add_const,
  ks_mk_const,
  mk_abs,
  mk_eq,
  mk_const,
  mk_var,
  term_alpha_eq,
  term_logical_eq,
  thm_concl,
}

///|
using @logic {
  type PropPrelude,
  type PropRefResolution,
  prop_dest_imp,
  prop_dest_and,
  prop_dest_or,
  logic_prop_context_apply_theorem,
  logic_prop_resolve_ref,
}

///|
using @logic {
  logic_prop_close_hypothesis,
  logic_prop_ensure_sequent,
  logic_prop_discharge_imp_prefix,
  logic_abs_rule,
  logic_deduct_antisym,
  logic_prop_truth_const_thm,
  logic_prop_replay_imp_elim_backward,
  logic_prop_replay_imp_elim_backward_thm,
  logic_prop_merge_conjunction,
  logic_prop_or_wrap_left,
  logic_prop_or_wrap_right,
  logic_beta_nf_bool_term_deep,
  logic_normalize_prop_beta,
}

///|
using @logic {
  default_prop_prelude,
  prop_mk_not,
  install_prop_prelude,
  prop_mk_imp,
  prop_mk_and,
  prop_mk_or,
}

///|
test "alias keepalive for tactics imports" {
  let _ : PropPrelude? = None
  let _ : PropRefResolution? = None
  let _ = empty_kernel_state
  let _ = bool_ty
  let _ = ks_add_const
  let _ = ks_mk_const
  let _ = mk_abs
  let _ = mk_eq
  let _ = mk_const
  let _ = mk_var
  let _ = term_alpha_eq
  let _ = term_logical_eq
  let _ = thm_concl
  let _ = prop_dest_imp
  let _ = prop_dest_and
  let _ = prop_dest_or
  let _ = logic_prop_context_apply_theorem
  let _ = logic_prop_resolve_ref
  let _ = logic_prop_close_hypothesis
  let _ = logic_prop_ensure_sequent
  let _ = logic_prop_discharge_imp_prefix
  let _ = logic_abs_rule
  let _ = logic_deduct_antisym
  let _ = logic_prop_truth_const_thm
  let _ = logic_prop_replay_imp_elim_backward
  let _ = logic_prop_replay_imp_elim_backward_thm
  let _ = logic_prop_merge_conjunction
  let _ = logic_prop_or_wrap_left
  let _ = logic_prop_or_wrap_right
  let _ = logic_beta_nf_bool_term_deep
  let _ = logic_normalize_prop_beta
  let _ = default_prop_prelude
  let _ = prop_mk_not
  let _ = install_prop_prelude
  let _ = prop_mk_imp
  let _ = prop_mk_and
  let _ = prop_mk_or
}
