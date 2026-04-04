///|
fn expect_cmd_success(result : CmdRunResult) -> CmdSuccess {
  match result {
    Success(ok) => ok
    Failure(_) => panic()
  }
}

///|
fn expect_cmd_failure(result : CmdRunResult) -> CmdFailure {
  match result {
    Success(_) => panic()
    Failure(err) => err
  }
}

///|
fn tmp_test_path(name : String) -> String {
  "/tmp/qed_cmd_" + name + ".qed"
}

///|
test "cmd run script succeeds on shipped single-theorem prelude script" {
  let src = "theorem truth_ok : ⊢ T := by exact truth"
  let result = cmd_run_script("truth_ok.qed", src, default_cmd_options())
  let ok = expect_cmd_success(result)
  let (_st, th) = match
    @prover.prove_theorem_script(
      @kernel.empty_kernel_state(),
      src,
      @prover.default_prover_options(),
    ) {
    Ok(v) => v
    Err(_) => panic()
  }
  let concl = match @kernel.thm_concl(th) {
    Ok(v) => v
    Err(_) => panic()
  }
  assert_eq(ok.path, "truth_ok.qed")
  assert_eq(ok.theorem_name, "truth_ok")
  assert_true(@kernel.term_logical_eq(ok.conclusion, concl))
  assert_eq(ok.conclusion_summary, @kernel.term_to_string(concl))
  assert_eq(
    cmd_render_result(result),
    "ok truth_ok: " + @kernel.term_to_string(concl),
  )
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd run script reports parse failures with raw offset detail" {
  let result = cmd_run_script(
    "parse_fail.qed",
    "theorem t : ⊢ T := by ; exact truth",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.path, "parse_fail.qed")
  assert_true(err.theorem_name is None)
  assert_true(err.step_index is None)
  assert_true(err.current_goal_summary is None)
  assert_eq(err.local_hyps.length(), 0)
  assert_eq(cmd_failure_kind_to_string(err.kind), "parse")
  assert_true(err.detail.contains("offset "))
  assert_true(cmd_render_result(result).contains("error[parse]"))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script reports stable tactic context for later-step failures" {
  let result = cmd_run_script(
    "step_fail.qed",
    "theorem bad : ⊢ T -> T := by intro h; apply truth",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.path, "step_fail.qed")
  assert_eq(err.theorem_name, Some("bad"))
  assert_eq(err.step_index, Some(2))
  assert_eq(cmd_failure_kind_to_string(err.kind), "tactic")
  assert_true(err.current_goal_summary is Some(_))
  assert_eq(err.local_hyps.length(), 1)
  assert_eq(err.local_hyps[0].name, "h")
  assert_true(err.local_hyps[0].term_summary.contains("Const(T"))
  assert_true(err.detail.contains("ApplyMismatch"))
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("step_fail.qed (bad)"))
  assert_true(rendered.contains("error[tactic]"))
  assert_true(rendered.contains("\nstep: 2"))
  assert_true(rendered.contains("\ngoal: ["))
  assert_true(rendered.contains("\nlocals: h:"))
}

///|
test "cmd run script renders explicit empty local summary when no locals exist" {
  let result = cmd_run_script(
    "no_locals_fail.qed",
    "theorem bad : ⊢ T := by apply truth",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.step_index, Some(1))
  assert_true(err.current_goal_summary is Some(_))
  assert_eq(err.local_hyps.length(), 0)
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("\nstep: 1"))
  assert_true(rendered.contains("\nlocals: <none>"))
}

///|
test "cmd argv reports usage and io failures" {
  let usage_result = cmd_run_argv(["qed-cmd"], default_cmd_options())
  let usage_err = expect_cmd_failure(usage_result)
  assert_eq(usage_err.path, "<cli>")
  assert_eq(cmd_failure_kind_to_string(usage_err.kind), "usage")
  assert_eq(usage_err.detail, "usage: qed-cmd <file>")

  let io_result = cmd_run_argv(
    ["qed-cmd", "/tmp/qed_cmd_missing_file.qed"],
    default_cmd_options(),
  )
  let io_err = expect_cmd_failure(io_result)
  assert_eq(io_err.path, "/tmp/qed_cmd_missing_file.qed")
  assert_eq(cmd_failure_kind_to_string(io_err.kind), "io")
}

///|
test "cmd argv reads single theorem file and returns success" {
  let path = tmp_test_path("argv_success")
  @fs.write_string_to_file(path, "theorem truth_file : ⊢ T := by exact truth")
  let result = cmd_run_argv(["qed-cmd", path], default_cmd_options())
  let ok = expect_cmd_success(result)
  assert_eq(ok.path, path)
  assert_eq(ok.theorem_name, "truth_file")
  assert_true(ok.conclusion_summary.contains("Const(T"))
  if @fs.path_exists(path) {
    @fs.remove_file(path)
  }
}
