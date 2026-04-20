///|
/// Blackbox test alias mirror for parser.
/// Mirror the production parser entry first, then add test-only imports below.
using @kernel {
  type KernelState,
  type Term,
  type Thm,
  bool_ty,
  empty_kernel_state,
  mk_tyvar,
  mk_var,
  fun_ty,
  ks_add_const,
  type_of,
  dest_var,
  dest_const,
  refl_checked,
  to_db_term,
  db_term_to_string,
  thm_concl,
  dest_eq,
  ks_pop_scope,
  ks_push_scope,
  term_alpha_eq,
  ty_eq,
}

///|
using @elab {
  elab_lower_to_term,
  empty_elab_ctx,
  elab_core_type_of,
  rconst_id,
  rterm_const,
}

///|
using @logic {install_prop_prelude}

///|
using @parser {parsed_goal_concl, parsed_goal_hyps}
