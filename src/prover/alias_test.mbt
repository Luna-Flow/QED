///|
/// Blackbox test package: full `using` union (main `alias.mbt` is not in scope here).
using @kernel {
  type KernelState,
  type Thm,
  type SigError,
  type LogicError,
  bool_ty,
  fun_ty,
  empty_kernel_state,
  ks_add_const,
  ks_mk_const,
  ks_push_scope,
  thm_concl,
  term_logical_eq,
}

///|
using @parser {
  type ParseError,
  type ParseBridgeError,
  type SynTacticStep,
  empty_parse_env,
  parse_theorem_script_raw,
  lower_syn_goal_with_env,
}

///|
using @tactics {
  type TacticStep,
  type TacticExecError,
  ps_init,
  ps_apply_script,
  ps_qed,
  step_intro,
  step_exact,
  step_apply,
  step_assumption,
  step_split,
  step_left,
  step_right,
}

///|
using @logic {
  install_prop_prelude,
  default_prop_prelude,
  prop_mk_imp,
  prop_mk_and,
}
