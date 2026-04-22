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
}

///|
using @parser {
  type ParseError,
  type ParseBridgeError,
  type SourceSpan,
  type SynScriptBody,
  type SynScriptStep,
  type SynTheoremScript,
  type SynTacticStep,
  empty_parse_env,
  parse_env_push_local,
  parse_theorem_file_raw,
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
  local_hyp_name,
  local_hyp_term,
  mk_goal,
  ps_apply,
  ps_current_local_hyps,
  ps_current_branch_path,
  ps_goal_count,
  ps_init,
  ps_isolate_pending_at,
  ps_close_current_with_th,
  ps_close_frame,
  ps_current_goal,
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
using @logic {type PropPrelude, install_prop_prelude, default_prop_prelude}
