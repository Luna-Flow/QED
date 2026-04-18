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
using @tactics {type Goal, goal_hyps, goal_concl, mk_goal}

///|
using @logic {
  install_prop_prelude,
  default_prop_prelude,
  logic_beta_nf_bool_term_deep,
  prop_mk_imp,
  prop_mk_and,
}

///|
using @prover {
  type PositiveCorpusCase,
  type NegativeCorpusCase,
  type MappingCaseKind,
  type MappingDocVisibility,
  type MappingMatrixEntry,
  type ProverFailure,
  type ProverRunResult,
  type ProverSuccess,
  type ProverUnfinished,
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
  prover_local_hyp,
  prover_unfinished,
}
