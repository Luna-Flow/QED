///|
/// Production alias entry for prover sources.
/// Prover may depend on parser-owned lowering results and explicitly bridge them
/// into tactics execution objects; it should not widen lower-layer export sets.
using @kernel {
  type KernelState,
  type Term,
  type Thm,
  type SigError,
  type LogicError,
  term_alpha_eq,
  term_logical_eq,
}

///|
using @parser {
  type ParseError,
  type ParseBridgeError,
  type SourceSpan,
  type SynScriptBody,
  type SynScriptStep,
  type SynTacticStep,
  empty_parse_env,
  parse_env_push_local,
  parse_theorem_script_raw,
  lower_syn_goal_with_env,
  parsed_goal_hyps,
  parsed_goal_concl,
}

///|
using @elab {type ElabError}

///|
using @tactics {
  type Goal,
  type ProofState,
  type TacticStep,
  type TacticExecError,
  goal_hyps,
  goal_concl,
  local_hyp_name,
  local_hyp_term,
  mk_goal,
  ps_apply,
  ps_current_local_hyps,
  ps_current_branch_path,
  ps_goal_count,
  ps_init,
  ps_current_goal,
  ps_pending_goal_at,
  ps_qed,
  tactic_goal_shape_mismatch,
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
  type PropPrelude,
  install_prop_prelude,
  default_prop_prelude,
  logic_beta_nf_bool_term_deep,
}
