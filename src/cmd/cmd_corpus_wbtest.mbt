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
fn unfinished_cases() -> Array[@prover.UnfinishedCorpusCase] {
  let out : Array[@prover.UnfinishedCorpusCase] = []
  for case in @prover.unfinished_corpus_cases() {
    out.push(case)
  }
  out
}

///|
fn quantifier_cases() -> Array[@prover.QuantifierCorpusCase] {
  let out : Array[@prover.QuantifierCorpusCase] = []
  for case in @prover.quantifier_corpus_cases() {
    out.push(case)
  }
  out
}

///|
fn render_branch_path_test(branch_path : Array[Int]) -> String {
  if branch_path.length() == 0 {
    "<root>"
  } else {
    branch_path.map(fn(idx) { idx.to_string() }).join(".")
  }
}

///|
fn render_local_hyps_test(local_hyps : Array[CmdLocalHypSummary]) -> String {
  if local_hyps.length() == 0 {
    "<none>"
  } else {
    local_hyps.map(fn(hyp) { hyp.name + ": " + hyp.term_summary }).join(", ")
  }
}

///|
fn render_hole_name_test(hole_name : String?) -> String {
  match hole_name {
    Some(name) => name
    None => "<none>"
  }
}

///|
fn expect_single_report_failure(result : CmdRunResult) -> CmdFailure {
  match result {
    FileReport(report) =>
      if report.items.length() == 1 {
        match report.items[0] {
          CmdItemFailure(err) => err
          _ => panic()
        }
      } else {
        panic()
      }
    Failure(err) => err
    Unfinished(_) => panic()
  }
}

///|
fn expect_single_report_warning(result : CmdRunResult) -> CmdUnfinished {
  match result {
    FileReport(report) =>
      if report.items.length() == 1 {
        match report.items[0] {
          CmdItemWarning(unfinished) => unfinished
          _ => panic()
        }
      } else {
        panic()
      }
    Failure(_) => panic()
    Unfinished(unfinished) => unfinished
  }
}

///|
fn expected_quantifier_local_count(_case_id : String) -> Int {
  1
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
      FileReport(report) => {
        assert_eq(report.path, case.case_id + ".qed")
        assert_eq(report.items.length(), 1)
        match report.items[0] {
          CmdItemSuccess(ok) => assert_eq(ok.theorem_name, case.case_id)
          _ => panic()
        }
        assert_eq(cmd_render_result(result), "ok " + case.case_id)
      }
      Failure(_) => panic()
      Unfinished(_) => panic()
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
    let err = expect_single_report_failure(result)
    assert_eq(err.path, case.case_id + ".qed")
    assert_eq(err.theorem_name, Some(case.case_id))
    assert_eq(
      cmd_failure_kind_to_string(err.kind),
      expected_cmd_kind_label_for_negative(case.expected_error),
    )
    assert_true(err.step_index is Some(_))
    assert_true(err.current_goal_summary is Some(_))
  }
}

///|
test "cmd unfinished corpus subset stays aligned with prover corpus" {
  let cases = unfinished_cases()
  assert_eq(cases.length(), 2)
  for case in cases {
    assert_true(
      @prover.mapping_matrix_entries().any(fn(entry) {
        entry.case_id == case.case_id
      }),
    )
    let result = cmd_run_script(
      case.case_id + ".qed",
      case.script,
      default_cmd_options(),
    )
    let unfinished = expect_single_report_warning(result)
    assert_eq(unfinished.path, case.case_id + ".qed")
    assert_eq(unfinished.theorem_name, case.case_id)
    assert_eq(unfinished.step_index, Some(case.expected_step_index))
    assert_eq(unfinished.branch_path, case.expected_branch_path)
    assert_eq(unfinished.hole_name, case.expected_hole_name)
    assert_eq(unfinished.detail, case.expected_detail)
    assert_true(unfinished.current_goal_summary.contains("|-"))
    let expected = [
      "warning[unfinished] " +
      case.case_id +
      ".qed (" +
      case.case_id +
      "): " +
      case.expected_detail,
      "theorem: " + case.case_id,
      "step: " + case.expected_step_index.to_string(),
      "branch: " + render_branch_path_test(case.expected_branch_path),
      "goal: " + unfinished.current_goal_summary,
      "locals: " + render_local_hyps_test(unfinished.local_hyps),
      "hole: " + render_hole_name_test(case.expected_hole_name),
      "message: " + case.expected_detail,
    ].join("\n")
    assert_eq(cmd_render_result(result), expected)
    assert_eq(cmd_exit_code(result), 1)
  }
}

///|
test "cmd quantifier corpus subset stays aligned with prover corpus" {
  let cases = quantifier_cases()
  assert_eq(cases.length(), 8)
  for case in cases {
    assert_true(
      @prover.mapping_matrix_entries().any(fn(entry) {
        entry.case_id == case.case_id
      }),
    )
    let result = cmd_run_script(
      case.case_id + ".qed",
      case.script,
      default_cmd_options(),
    )
    let outcome = @prover.quantifier_surface_outcome_label(case.outcome)
    if outcome == "success" {
      match result {
        FileReport(report) => {
          assert_eq(report.path, case.case_id + ".qed")
          assert_eq(report.items.length(), 1)
          match report.items[0] {
            CmdItemSuccess(ok) => assert_eq(ok.theorem_name, case.case_id)
            _ => panic()
          }
          assert_eq(cmd_render_result(result), "ok " + case.case_id)
        }
        Failure(_) => {
          println("quantifier success case failed: " + case.case_id)
          println(cmd_render_result(result))
          panic()
        }
        Unfinished(_) => panic()
      }
    } else if outcome == "failure" {
      let err = expect_single_report_failure(result)
      let expected_step_index = match case.expected_step_index {
        Some(v) => v
        None => panic()
      }
      let expected_detail = match case.expected_detail {
        Some(v) => v
        None => panic()
      }
      assert_eq(err.path, case.case_id + ".qed")
      assert_eq(err.theorem_name, Some(case.case_id))
      assert_eq(cmd_failure_kind_to_string(err.kind), "tactic")
      assert_eq(err.step_index, case.expected_step_index)
      assert_eq(err.branch_path, case.expected_branch_path)
      assert_true(err.current_goal_summary is Some(_))
      assert_eq(
        err.local_hyps.length(),
        expected_quantifier_local_count(case.case_id),
      )
      assert_true(err.detail.contains(expected_detail))
      let rendered = cmd_render_result(result)
      assert_true(rendered.contains("error[tactic]"))
      assert_true(
        rendered.contains("\nstep: " + expected_step_index.to_string()),
      )
      assert_true(
        rendered.contains(
          "\nbranch: " + render_branch_path_test(case.expected_branch_path),
        ),
      )
      assert_true(rendered.contains("\ngoal: "))
      assert_true(rendered.contains("\nlocals: "))
      assert_true(rendered.contains("x : bool"))
      if case.case_id.contains("_forall_") {
        assert_true(rendered.contains("h: Var(x : bool)"))
      }
    } else {
      let unfinished = expect_single_report_warning(result)
      let expected_detail = match case.expected_detail {
        Some(v) => v
        None => panic()
      }
      let expected_step_index = match case.expected_step_index {
        Some(v) => v
        None => panic()
      }
      assert_eq(unfinished.path, case.case_id + ".qed")
      assert_eq(unfinished.theorem_name, case.case_id)
      assert_eq(unfinished.step_index, case.expected_step_index)
      assert_eq(unfinished.branch_path, case.expected_branch_path)
      assert_eq(unfinished.hole_name, case.expected_hole_name)
      assert_eq(unfinished.detail, expected_detail)
      assert_true(unfinished.current_goal_summary.contains("|-"))
      let expected = [
        "warning[unfinished] " +
        case.case_id +
        ".qed (" +
        case.case_id +
        "): " +
        expected_detail,
        "theorem: " + case.case_id,
        "step: " + expected_step_index.to_string(),
        "branch: " + render_branch_path_test(case.expected_branch_path),
        "goal: " + unfinished.current_goal_summary,
        "locals: " + render_local_hyps_test(unfinished.local_hyps),
        "hole: " + render_hole_name_test(case.expected_hole_name),
        "message: " + expected_detail,
      ].join("\n")
      assert_eq(cmd_render_result(result), expected)
      assert_eq(cmd_exit_code(result), 1)
    }
  }
}
