///|
/// Blackbox test alias mirror for prover.
/// Reproduce the production entry first, then append test-only imports.
using @kernel {
  type KernelState,
  type Thm,
  type Term,
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
using @parser {parsed_goal_concl, parsed_goal_hyps, parse_goal, source_span}

///|
using @parser {empty_parse_env, parse_env_push_local, parse_goal_with_env}

///|
using @tactics {
  type Goal,
  goal_hyps,
  goal_concl,
  mk_goal,
  ps_init,
  ps_apply,
  ps_qed,
  step_intro,
  step_exact,
}

///|
using @logic {
  install_prop_prelude,
  default_prop_prelude,
  logic_abs_rule,
  logic_beta_nf_bool_term_deep,
  logic_deduct_antisym,
  prop_mk_imp,
  prop_mk_and,
  logic_prop_truth_const_thm,
}

///|
using @prover {
  type PositiveCorpusCase,
  type UnfinishedCorpusCase,
  type QuantifierCorpusCase,
  type NegativeCorpusCase,
  type MappingCaseKind,
  type MappingDocVisibility,
  type MappingMatrixEntry,
  type ProverFailure,
  type ProverRunResult,
  type ProverScriptError,
  type ProverSuccess,
  type ProverUnfinished,
  positive_corpus_cases,
  unfinished_corpus_cases,
  quantifier_corpus_cases,
  negative_corpus_cases,
  mapping_matrix_entries,
  mapping_case_positive,
  mapping_case_negative,
  mapping_case_unfinished,
  mapping_doc_visibility_public_example,
  mapping_doc_visibility_public_failure_example,
  mapping_doc_visibility_public_unfinished_example,
  catalog_label,
  capability_label,
  negative_failure_class_label,
  negative_error_shape_label,
  prove_theorem_script_detailed,
  prove_theorem_script_with_diagnostics,
  prover_local_hyp,
  prover_unfinished,
}
