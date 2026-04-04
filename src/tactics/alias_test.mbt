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
  mk_const,
  mk_var,
  term_alpha_eq,
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
