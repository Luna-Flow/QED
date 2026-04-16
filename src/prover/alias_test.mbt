///|
/// Blackbox test package: full `using` union (main `alias.mbt` is not in scope here).
using @kernel {
  type KernelState,
  type Thm,
  type Term,
  type SigError,
  type LogicError,
  bool_ty,
  fun_ty,
  empty_kernel_state,
  ks_add_const,
  ks_mk_const,
  ks_push_scope,
  mk_var,
  thm_concl,
  thm_hyps,
  term_logical_eq,
  term_alpha_eq,
}

///|
using @parser {
  type ParseError,
  type ParseBridgeError,
  type SynTacticStep,
  empty_parse_env,
  parse_goal,
  parse_theorem_script_raw,
  lower_syn_goal_with_env,
}

///|
using @tactics {
  type Goal,
  type TacticStep,
  type TacticExecError,
  goal_hyps,
  goal_concl,
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
  type PropPrelude,
  install_prop_prelude,
  default_prop_prelude,
  logic_beta_nf_bool_term_deep,
  prop_dest_imp,
  prop_dest_or,
  prop_mk_imp,
  prop_mk_and,
}

///|
using @prover {
  type ScriptLayout,
  type PositiveCorpusCase,
  type NegativeCorpusCase,
  type MappingCaseKind,
  type MappingDocVisibility,
  type MappingMatrixEntry,
  type ProverDiagnosticKind,
  type ProverFailure,
  type ProverRunResult,
  type ProverSuccess,
  script_layout_label,
  positive_corpus_cases,
  negative_corpus_cases,
  mapping_matrix_entries,
  mapping_case_positive,
  mapping_case_negative,
  mapping_doc_visibility_public_example,
  mapping_doc_visibility_public_failure_example,
  catalog_label,
  capability_label,
  negative_failure_class_label,
  negative_error_shape_label,
  prove_theorem_script_detailed,
  prove_theorem_script_with_diagnostics,
}
