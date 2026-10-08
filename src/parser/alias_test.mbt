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

///|
/// Package-local names used by blackbox tests; blackbox tests must import
/// them explicitly from `@parser`.
using @parser {
  type ParseBridgeError,
  type ParseError,
  type SynGoal,
  type SynScriptStep,
  type SynTacticStep,
  type SynTerm,
  empty_parse_env,
  normalize_parser_input,
  normalized_input_raw_offset_at,
  parse_def_function,
  parse_env_local_at,
  parse_env_local_count,
  parse_goal,
  parse_goal_raw,
  parse_goal_with_env,
  parse_let,
  parse_resolved_term_with_env,
  parse_term,
  parse_term_raw,
  parse_term_with_env,
  parse_theorem_file_raw,
  parse_theorem_script_raw,
}
