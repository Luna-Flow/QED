///|
fn[T, E] expect_ok_negative(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
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
fn corpus_covers_layout(
  cases : Array[NegativeCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) { script_layout_label(case.layout) == label })
}

///|
fn corpus_covers_case_id(
  cases : Array[NegativeCorpusCase],
  case_id : String,
) -> Bool {
  cases.any(fn(case) { case.case_id == case_id })
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
  assert_true(corpus_covers_layout(cases, "inline_sequential"))
  assert_true(corpus_covers_layout(cases, "block_sequential"))
  assert_true(corpus_covers_case_id(cases, "neg_apply_eq_refl_wrong_mode"))
  assert_true(
    corpus_covers_case_id(cases, "neg_local_shadow_truth_is_not_direct_witness"),
  )
  assert_true(corpus_covers_case_id(cases, "neg_block_apply_truth_wrong_mode"))
}
