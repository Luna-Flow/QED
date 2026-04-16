///|
fn state_free_positive_cases() -> Array[@prover.PositiveCorpusCase] {
  let out : Array[@prover.PositiveCorpusCase] = []
  for case in @prover.positive_corpus_cases() {
    if case.const_names.length() == 0 {
      out.push(case)
    }
  }
  out
}

///|
fn state_free_negative_cases() -> Array[@prover.NegativeCorpusCase] {
  let out : Array[@prover.NegativeCorpusCase] = []
  for case in @prover.negative_corpus_cases() {
    if case.bool_consts.length() == 0 &&
      case.unary_bool_consts.length() == 0 &&
      case.binary_bool_consts.length() == 0 {
      out.push(case)
    }
  }
  out
}

///|
fn expected_cmd_kind_label_for_negative(
  shape : @prover.NegativeErrorShape,
) -> String {
  match @prover.negative_error_shape_label(shape) {
    "logic_not_bool_term" => "logic"
    _ => "tactic"
  }
}

///|
fn mapping_contains_case(case_id : String) -> Bool {
  @prover.mapping_matrix_entries().any(fn(entry) { entry.case_id == case_id })
}

///|
test "cmd state-free positive corpus subset stays aligned with prover corpus" {
  let cases = state_free_positive_cases()
  assert_eq(cases.length(), 2)
  for case in cases {
    assert_true(mapping_contains_case(case.case_id))
    let result = cmd_run_script(
      case.case_id + ".qed",
      case.script,
      default_cmd_options(),
    )
    match result {
      Success(ok) => {
        assert_eq(ok.path, case.case_id + ".qed")
        assert_eq(ok.theorem_name, case.case_id)
        assert_true(
          cmd_render_result(result).contains("ok " + case.case_id + ":"),
        )
      }
      Failure(_) => panic()
    }
  }
}

///|
test "cmd state-free negative corpus subset preserves expected failure kinds" {
  let cases = state_free_negative_cases()
  assert_eq(cases.length(), 2)
  for case in cases {
    assert_true(mapping_contains_case(case.case_id))
    let result = cmd_run_script(
      case.case_id + ".qed",
      case.script,
      default_cmd_options(),
    )
    match result {
      Failure(err) => {
        assert_eq(err.path, case.case_id + ".qed")
        assert_eq(err.theorem_name, Some(case.case_id))
        assert_eq(
          cmd_failure_kind_to_string(err.kind),
          expected_cmd_kind_label_for_negative(case.expected_error),
        )
        assert_true(err.step_index is Some(_))
        assert_true(err.current_goal_summary is Some(_))
      }
      Success(_) => panic()
    }
  }
}
