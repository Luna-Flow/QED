///|
/// Blackbox test package imports for the research rewrite prototype.
using @kernel {
  type KernelState,
  type Term,
  empty_kernel_state,
  bool_ty,
  fun_ty,
  mk_tyvar,
  mk_var,
  ks_mk_const,
  mk_abs,
  mk_comb,
  mk_eq,
  term_alpha_eq,
}

///|
using @logic {
  type PropPrelude,
  default_prop_prelude,
  install_prop_prelude,
  logic_assume,
  prop_mk_and,
}

///|
using @research_rewrite {
  type ReplayStepKind,
  research_rewrite_request,
  research_local_equality,
  research_explicit_theorem,
  research_canonical_unfold_and,
  research_beta_normalization,
  research_left_to_right,
  research_right_to_left,
  research_site_comb_arg,
  research_site_abs_body,
  research_replay_obligation,
  research_simplify_config,
  research_step_name,
  research_rewrite_term_concl,
  research_validate_replay_obligation,
  research_simplify_term_concl,
}
