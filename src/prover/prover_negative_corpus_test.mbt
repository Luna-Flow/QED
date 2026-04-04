///|
enum NegativeFailureClass {
  FailureUnknownName
  FailureWrongModeTheoremUsage
  FailureGoalShapeMismatch
  FailureNonBoolConnector
  FailureUnsupportedHonestFailure
  FailureShadowingOrScopeDrift
}

///|
enum NegativeErrorShape {
  ErrorTacticUnknownName
  ErrorTacticApplyMismatch
  ErrorTacticGoalShapeMismatch
  ErrorTacticUnsolvedGoals
  ErrorLogicNotBoolTerm
}

///|
struct NegativeCorpusCase {
  case_id : String
  bool_consts : Array[String]
  unary_bool_consts : Array[String]
  binary_bool_consts : Array[String]
  script : String
  failure_class : NegativeFailureClass
  expected_error : NegativeErrorShape
}

///|
fn[T, E] expect_ok_negative(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn negative_failure_class_label(cls : NegativeFailureClass) -> String {
  match cls {
    FailureUnknownName => "unknown_name"
    FailureWrongModeTheoremUsage => "wrong_mode_theorem_usage"
    FailureGoalShapeMismatch => "goal_shape_mismatch"
    FailureNonBoolConnector => "non_bool_connector"
    FailureUnsupportedHonestFailure => "unsupported_honest_failure"
    FailureShadowingOrScopeDrift => "shadowing_or_scope_drift"
  }
}

///|
fn negative_error_shape_label(shape : NegativeErrorShape) -> String {
  match shape {
    ErrorTacticUnknownName => "tactic_unknown_name"
    ErrorTacticApplyMismatch => "tactic_apply_mismatch"
    ErrorTacticGoalShapeMismatch => "tactic_goal_shape_mismatch"
    ErrorTacticUnsolvedGoals => "tactic_unsolved_goals"
    ErrorLogicNotBoolTerm => "logic_not_bool_term"
  }
}

///|
fn build_negative_state(case : NegativeCorpusCase) -> KernelState {
  let mut st = empty_kernel_state()
  for name in case.bool_consts {
    st = expect_ok_negative(ks_add_const(st, name, bool_ty()))
  }
  for name in case.unary_bool_consts {
    st = expect_ok_negative(
      ks_add_const(st, name, fun_ty(bool_ty(), bool_ty())),
    )
  }
  for name in case.binary_bool_consts {
    st = expect_ok_negative(
      ks_add_const(st, name, fun_ty(bool_ty(), fun_ty(bool_ty(), bool_ty()))),
    )
  }
  st
}

///|
fn negative_corpus_cases() -> Array[NegativeCorpusCase] {
  [
    NegativeCorpusCase::{
      case_id: "neg_unknown_exact_name",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unknown_exact_name : ⊢ P -> P := by exact missing",
      failure_class: FailureUnknownName,
      expected_error: ErrorTacticUnknownName,
    },
    NegativeCorpusCase::{
      case_id: "neg_unknown_apply_name",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unknown_apply_name : ⊢ P := by apply missing",
      failure_class: FailureUnknownName,
      expected_error: ErrorTacticUnknownName,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_truth_wrong_mode",
      bool_consts: [],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_truth_wrong_mode : ⊢ T := by apply truth",
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_ex_falso_wrong_mode",
      bool_consts: ["Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_ex_falso_wrong_mode : F ⊢ Q := by apply ex_falso",
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_exact_or_intro_wrong_mode",
      bool_consts: ["P", "Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_exact_or_intro_wrong_mode : ⊢ P -> P ∨ Q := by exact or_intro_l",
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_and_elim_goal_mismatch",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_and_elim_goal_mismatch : ⊢ P := by apply and_elim_l",
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_intro_non_implication_goal",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_intro_non_implication_goal : ⊢ P := by intro h",
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_exact_context_missing",
      bool_consts: ["P", "Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_exact_context_missing : P ⊢ P := by exact and_elim_l",
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_non_bool_connector_rejected",
      bool_consts: ["Q"],
      unary_bool_consts: ["f"],
      binary_bool_consts: [],
      script: "theorem neg_non_bool_connector_rejected : ⊢ f ∧ Q := by exact truth",
      failure_class: FailureNonBoolConnector,
      expected_error: ErrorLogicNotBoolTerm,
    },
    NegativeCorpusCase::{
      case_id: "neg_unsolved_script_is_honest_failure",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unsolved_script_is_honest_failure : ⊢ P -> P := by intro h",
      failure_class: FailureUnsupportedHonestFailure,
      expected_error: ErrorTacticUnsolvedGoals,
    },
    NegativeCorpusCase::{
      case_id: "neg_ordinary_imp_not_trusted",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: ["my_imp"],
      script: "theorem neg_ordinary_imp_not_trusted : ⊢ my_imp P P := by intro h; exact h",
      failure_class: FailureUnsupportedHonestFailure,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_local_shadow_truth_is_not_implication",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_local_shadow_truth_is_not_implication : ⊢ P -> P := by intro truth; apply truth",
      failure_class: FailureShadowingOrScopeDrift,
      expected_error: ErrorTacticApplyMismatch,
    },
  ]
}

///|
fn negative_case_ids_are_unique(cases : Array[NegativeCorpusCase]) -> Bool {
  let seen : Array[String] = []
  for case in cases {
    if seen.contains(case.case_id) {
      return false
    }
    seen.push(case.case_id)
  }
  true
}

///|
fn negative_result_matches(
  res : Result[(KernelState, Thm), ProverError],
  expected : NegativeErrorShape,
) -> Bool {
  match expected {
    ErrorTacticUnknownName => res is Err(Tactic(UnknownName(_)))
    ErrorTacticApplyMismatch => res is Err(Tactic(ApplyMismatch(_)))
    ErrorTacticGoalShapeMismatch => res is Err(Tactic(GoalShapeMismatch(_)))
    ErrorTacticUnsolvedGoals => res is Err(Tactic(UnsolvedGoals))
    ErrorLogicNotBoolTerm => res is Err(Logic(NotBoolTerm))
  }
}

///|
fn corpus_covers_failure_class(
  cases : Array[NegativeCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) {
    negative_failure_class_label(case.failure_class) == label
  })
}

///|
fn corpus_covers_error_shape(
  cases : Array[NegativeCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) {
    negative_error_shape_label(case.expected_error) == label
  })
}

///|
test "prove_theorem_script canonical negative corpus stays honest" {
  let cases = negative_corpus_cases()
  for case in cases {
    let st = build_negative_state(case)
    let res = prove_theorem_script(st, case.script, default_prover_options())
    assert_true(
      negative_result_matches(res, case.expected_error),
      msg="negative corpus case `" +
        case.case_id +
        "` failed to produce class `" +
        negative_failure_class_label(case.failure_class) +
        "` with error `" +
        negative_error_shape_label(case.expected_error) +
        "`",
    )
  }
}

///|
test "prove_theorem_script canonical negative corpus covers planned failure classes" {
  let cases = negative_corpus_cases()
  assert_true(negative_case_ids_are_unique(cases))
  assert_true(corpus_covers_failure_class(cases, "unknown_name"))
  assert_true(corpus_covers_failure_class(cases, "wrong_mode_theorem_usage"))
  assert_true(corpus_covers_failure_class(cases, "goal_shape_mismatch"))
  assert_true(corpus_covers_failure_class(cases, "non_bool_connector"))
  assert_true(corpus_covers_failure_class(cases, "unsupported_honest_failure"))
  assert_true(corpus_covers_failure_class(cases, "shadowing_or_scope_drift"))
  assert_true(corpus_covers_error_shape(cases, "tactic_unknown_name"))
  assert_true(corpus_covers_error_shape(cases, "tactic_apply_mismatch"))
  assert_true(corpus_covers_error_shape(cases, "tactic_goal_shape_mismatch"))
  assert_true(corpus_covers_error_shape(cases, "tactic_unsolved_goals"))
  assert_true(corpus_covers_error_shape(cases, "logic_not_bool_term"))
}
