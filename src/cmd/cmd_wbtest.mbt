///|
fn expect_cmd_success(result : CmdRunResult) -> CmdSuccess {
  match result {
    FileReport(report) =>
      if report.items.length() == 1 {
        match report.items[0] {
          CmdItemSuccess(ok) => ok
          _ => panic()
        }
      } else {
        panic()
      }
    Failure(_) => panic()
    Unfinished(_) => panic()
  }
}

///|
fn expect_cmd_file_report(result : CmdRunResult) -> CmdFileReport {
  match result {
    FileReport(report) => report
    Failure(_) => panic()
    Unfinished(_) => panic()
  }
}

///|
fn expect_cmd_failure(result : CmdRunResult) -> CmdFailure {
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
fn expect_cmd_unfinished(result : CmdRunResult) -> CmdUnfinished {
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
fn tmp_test_path(name : String) -> String {
  "/tmp/qed_cmd_" + name + ".qed"
}

///|
test "cmd failure kind labels stay stable" {
  assert_eq(cmd_failure_kind_to_string(Usage), "usage")
  assert_eq(cmd_failure_kind_to_string(Io), "io")
  assert_eq(cmd_failure_kind_to_string(Parse), "parse")
  assert_eq(cmd_failure_kind_to_string(Bridge), "bridge")
  assert_eq(cmd_failure_kind_to_string(Tactic), "tactic")
  assert_eq(cmd_failure_kind_to_string(Sig), "sig")
  assert_eq(cmd_failure_kind_to_string(Logic), "logic")
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
  assert_eq(cmd_render_result(result), "ok truth_ok")
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd run script renders detailed success when requested" {
  let src = "theorem truth_ok : ⊢ T := by exact truth"
  let result = cmd_run_script(
    "truth_ok.qed",
    src,
    cmd_options_with_detail(true, true),
  )
  let ok = expect_cmd_success(result)
  assert_true(cmd_render_result(result).contains("ok truth_ok: "))
  assert_true(cmd_render_result(result).contains(ok.conclusion_summary))
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd run script succeeds on multiple qed-terminated theorem blocks" {
  let src = "theorem first : ⊢ T := by exact truth\nqed\n\ntheorem second : ⊢ T := by exact truth\nqed"
  let result = cmd_run_script("multi.qed", src, default_cmd_options())
  let report = expect_cmd_file_report(result)
  assert_eq(report.path, "multi.qed")
  assert_eq(report.items.length(), 2)
  assert_true(report.items[0] is CmdItemSuccess(_))
  assert_true(report.items[1] is CmdItemSuccess(_))
  assert_eq(cmd_render_result(result), "ok first\nok second")
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd run script renders multiple detailed successes when requested" {
  let src = "theorem first : ⊢ T := by exact truth\nqed\n\ntheorem second : ⊢ T := by exact truth\nqed"
  let result = cmd_run_script(
    "multi.qed",
    src,
    cmd_options_with_detail(true, true),
  )
  let report = expect_cmd_file_report(result)
  let rendered = cmd_render_result(result)
  assert_eq(report.items.length(), 2)
  assert_true(rendered.contains("ok first: "))
  assert_true(rendered.contains("ok second: "))
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd run script reports unfinished as warning and continues" {
  let src = "theorem first : ⊢ T := by exact truth\nqed\n\ntheorem holey : ⊢ T := by hole h1\nqed\n\ntheorem second : ⊢ T := by exact truth\nqed"
  let result = cmd_run_script("multi_warn.qed", src, default_cmd_options())
  let report = expect_cmd_file_report(result)
  assert_eq(report.items.length(), 3)
  assert_true(report.items[0] is CmdItemSuccess(_))
  assert_true(report.items[1] is CmdItemWarning(_))
  assert_true(report.items[2] is CmdItemSuccess(_))
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("ok first"))
  assert_true(rendered.contains("warning[unfinished] multi_warn.qed (holey)"))
  assert_true(rendered.contains("ok second"))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd no-warn keeps warning visible but allows warning-only exit success" {
  let src = "theorem first : ⊢ T := by exact truth\nqed\n\ntheorem holey : ⊢ T := by hole h1\nqed\n\ntheorem second : ⊢ T := by exact truth\nqed"
  let result = cmd_run_script(
    "multi_warn.qed",
    src,
    cmd_options_full(true, false, true),
  )
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("warning[unfinished] multi_warn.qed (holey)"))
  assert_true(rendered.contains("ok second"))
  assert_eq(cmd_exit_code(result), 0)
}

///|
test "cmd no-warn does not allow real errors" {
  let src = "theorem first : ⊢ T := by exact truth\nqed\n\ntheorem bad : ⊢ T -> T := by intro h; apply truth\nqed\n\ntheorem second : ⊢ T := by exact truth\nqed"
  let result = cmd_run_script(
    "multi_error.qed",
    src,
    cmd_options_full(true, false, true),
  )
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("ok first"))
  assert_true(rendered.contains("error[tactic] multi_error.qed (bad)"))
  assert_true(rendered.contains("ok second"))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script reports missing qed before later theorem" {
  let result = cmd_run_script(
    "multi_missing_qed.qed",
    "theorem first : ⊢ T := by exact truth\n\ntheorem second : ⊢ T := by exact truth",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.path, "multi_missing_qed.qed")
  assert_true(err.theorem_name is None)
  assert_eq(cmd_failure_kind_to_string(err.kind), "parse")
  assert_true(err.detail.contains("missing qed before next theorem"))
  assert_eq(cmd_exit_code(result), 1)
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
  assert_eq(cmd_exit_code(result), 1)
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
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script renders branch path for nested branch failures" {
  let result = cmd_run_script(
    "branch_fail.qed",
    "theorem bad : ⊢ T ∧ (F ∨ T) := by split { exact truth } { right { apply truth } }",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.step_index, Some(4))
  assert_eq(err.branch_path, [2, 1])
  let rendered = cmd_render_result(result)
  assert_true(rendered.contains("\nbranch: 2.1"))
  assert_true(rendered.contains("\nstep: 4"))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script keeps quantifier-facing binder failure rendering stable" {
  let result = cmd_run_script(
    "quant_fail.qed",
    "theorem quant_bad (x : bool) : ⊢ x -> x ∨ x := by intro h; left { exact truth }",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.path, "quant_fail.qed")
  assert_eq(err.theorem_name, Some("quant_bad"))
  assert_eq(err.step_index, Some(3))
  assert_eq(err.branch_path, [1])
  assert_eq(err.current_goal_summary, Some("[Var(x : bool)] |- Var(x : bool)"))
  assert_eq(err.local_hyps.length(), 1)
  assert_eq(err.local_hyps[0].name, "h")
  assert_eq(err.local_hyps[0].term_summary, "Var(x : bool)")
  let rendered = cmd_render_result(result)
  assert_eq(
    rendered,
    [
      "error[tactic] quant_fail.qed (quant_bad): " + err.detail,
      "step: 3",
      "branch: 1",
      "goal: [Var(x : bool)] |- Var(x : bool)",
      "locals: h: Var(x : bool)",
    ].join("\n"),
  )
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script keeps raw forall quantifier failure rendering stable" {
  let result = cmd_run_script(
    "quant_forall_fail.qed",
    "theorem quant_forall_bad : ⊢ forall (x : bool), x -> x ∨ x := by intro h; left { exact truth }",
    default_cmd_options(),
  )
  let err = expect_cmd_failure(result)
  assert_eq(err.path, "quant_forall_fail.qed")
  assert_eq(err.theorem_name, Some("quant_forall_bad"))
  assert_eq(err.step_index, Some(3))
  assert_eq(err.branch_path, [1])
  assert_eq(err.current_goal_summary, Some("[Var(x : bool)] |- Var(x : bool)"))
  assert_eq(err.local_hyps.length(), 1)
  assert_eq(err.local_hyps[0].name, "h")
  assert_eq(err.local_hyps[0].term_summary, "Var(x : bool)")
  let rendered = cmd_render_result(result)
  assert_eq(
    rendered,
    [
      "error[tactic] quant_forall_fail.qed (quant_forall_bad): " + err.detail,
      "step: 3",
      "branch: 1",
      "goal: [Var(x : bool)] |- Var(x : bool)",
      "locals: h: Var(x : bool)",
    ].join("\n"),
  )
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd unfinished helper renders stable unfinished contract" {
  let result = cmd_unfinished(
    "unfinished.qed",
    "cmd_hole",
    Some(4),
    [1, 2],
    "[] |- Const(T)",
    [CmdLocalHypSummary::{ name: "h", term_summary: "Const(T)" }],
    Some("h1"),
    "proof is unfinished",
  )
  let unfinished = expect_cmd_unfinished(result)
  assert_eq(unfinished.path, "unfinished.qed")
  assert_eq(unfinished.theorem_name, "cmd_hole")
  assert_eq(unfinished.step_index, Some(4))
  assert_eq(unfinished.branch_path, [1, 2])
  assert_true(unfinished.current_goal_summary.contains("|-"))
  assert_eq(unfinished.local_hyps.length(), 1)
  assert_eq(unfinished.local_hyps[0].name, "h")
  assert_eq(unfinished.hole_name, Some("h1"))
  assert_eq(unfinished.detail, "proof is unfinished")
  let rendered = cmd_render_result(result)
  assert_true(
    rendered.contains(
      "unfinished unfinished.qed (cmd_hole): proof is unfinished",
    ),
  )
  assert_true(rendered.contains("\ntheorem: cmd_hole"))
  assert_true(rendered.contains("\nstep: 4"))
  assert_true(rendered.contains("\nbranch: 1.2"))
  assert_true(rendered.contains("\ngoal: [] |- Const(T)"))
  assert_true(rendered.contains("\nlocals: h: Const(T)"))
  assert_true(rendered.contains("\nhole: h1"))
  assert_true(rendered.contains("\nmessage: proof is unfinished"))
  assert_false(rendered.contains("error["))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd unfinished rendering keeps empty markers stable" {
  let result = cmd_unfinished(
    "unfinished_root.qed",
    "cmd_hole",
    None,
    [],
    "[] |- Const(T)",
    [],
    None,
    "todo",
  )
  let unfinished = expect_cmd_unfinished(result)
  assert_eq(unfinished.theorem_name, "cmd_hole")
  let rendered = cmd_render_result(result)
  assert_true(
    rendered.contains("unfinished unfinished_root.qed (cmd_hole): todo"),
  )
  assert_true(rendered.contains("\ntheorem: cmd_hole"))
  assert_true(rendered.contains("\nstep: <none>"))
  assert_true(rendered.contains("\nbranch: <root>"))
  assert_true(rendered.contains("\ngoal: [] |- Const(T)"))
  assert_true(rendered.contains("\nlocals: <none>"))
  assert_true(rendered.contains("\nhole: <none>"))
  assert_true(rendered.contains("\nmessage: todo"))
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script keeps quantifier-facing binder unfinished rendering stable" {
  let result = cmd_run_script(
    "quant_unfinished.qed",
    "theorem quant_hole (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }",
    default_cmd_options(),
  )
  let unfinished = expect_cmd_unfinished(result)
  assert_eq(unfinished.path, "quant_unfinished.qed")
  assert_eq(unfinished.theorem_name, "quant_hole")
  assert_eq(unfinished.step_index, Some(4))
  assert_eq(unfinished.branch_path, [1, 1])
  assert_eq(unfinished.current_goal_summary, "[Var(x : bool)] |- Var(x : bool)")
  assert_eq(unfinished.local_hyps.length(), 1)
  assert_eq(unfinished.local_hyps[0].name, "h")
  assert_eq(unfinished.local_hyps[0].term_summary, "Var(x : bool)")
  assert_eq(unfinished.hole_name, Some("h1"))
  assert_eq(unfinished.detail, "proof contains an unfinished hole")
  let rendered = cmd_render_result(result)
  assert_eq(
    rendered,
    [
      "warning[unfinished] quant_unfinished.qed (quant_hole): proof contains an unfinished hole",
      "theorem: quant_hole", "step: 4", "branch: 1.1", "goal: [Var(x : bool)] |- Var(x : bool)",
      "locals: h: Var(x : bool)", "hole: h1", "message: proof contains an unfinished hole",
    ].join("\n"),
  )
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd run script keeps raw forall quantifier unfinished rendering stable" {
  let result = cmd_run_script(
    "quant_forall_unfinished.qed",
    "theorem quant_forall_hole : ⊢ forall (x : bool), x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }",
    default_cmd_options(),
  )
  let unfinished = expect_cmd_unfinished(result)
  assert_eq(unfinished.path, "quant_forall_unfinished.qed")
  assert_eq(unfinished.theorem_name, "quant_forall_hole")
  assert_eq(unfinished.step_index, Some(4))
  assert_eq(unfinished.branch_path, [1, 1])
  assert_eq(unfinished.current_goal_summary, "[Var(x : bool)] |- Var(x : bool)")
  assert_eq(unfinished.local_hyps.length(), 1)
  assert_eq(unfinished.local_hyps[0].name, "h")
  assert_eq(unfinished.local_hyps[0].term_summary, "Var(x : bool)")
  assert_eq(unfinished.hole_name, Some("h1"))
  assert_eq(unfinished.detail, "proof contains an unfinished hole")
  let rendered = cmd_render_result(result)
  assert_eq(
    rendered,
    [
      "warning[unfinished] quant_forall_unfinished.qed (quant_forall_hole): proof contains an unfinished hole",
      "theorem: quant_forall_hole", "step: 4", "branch: 1.1", "goal: [Var(x : bool)] |- Var(x : bool)",
      "locals: h: Var(x : bool)", "hole: h1", "message: proof contains an unfinished hole",
    ].join("\n"),
  )
  assert_eq(cmd_exit_code(result), 1)
}

///|
test "cmd argv reports usage and io failures" {
  let usage_result = cmd_run_argv(["qed-cmd"], default_cmd_options())
  let usage_err = expect_cmd_failure(usage_result)
  assert_eq(usage_err.path, "<cli>")
  assert_eq(cmd_failure_kind_to_string(usage_err.kind), "usage")
  assert_eq(usage_err.detail, "usage: qed-cmd [-d] [--no-warn] <file>")
  assert_eq(cmd_exit_code(usage_result), 1)

  let io_result = cmd_run_argv(
    ["qed-cmd", "/tmp/qed_cmd_missing_file.qed"],
    default_cmd_options(),
  )
  let io_err = expect_cmd_failure(io_result)
  assert_eq(io_err.path, "/tmp/qed_cmd_missing_file.qed")
  assert_eq(cmd_failure_kind_to_string(io_err.kind), "io")
  assert_eq(cmd_exit_code(io_result), 1)
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
  assert_eq(cmd_render_result(result), "ok truth_file")
  if @fs.path_exists(path) {
    @fs.remove_file(path)
  }
}

///|
test "cmd argv accepts detail flag before file" {
  let path = tmp_test_path("argv_detail_success")
  @fs.write_string_to_file(path, "theorem truth_file : ⊢ T := by exact truth")
  let result = cmd_run_argv(["qed-cmd", "-d", path], default_cmd_options())
  let ok = expect_cmd_success(result)
  assert_eq(ok.path, path)
  assert_eq(ok.theorem_name, "truth_file")
  assert_true(cmd_render_result(result).contains("ok truth_file: "))
  assert_true(cmd_render_result(result).contains(ok.conclusion_summary))
  if @fs.path_exists(path) {
    @fs.remove_file(path)
  }
}

///|
test "cmd argv accepts no-warn and detail flags in either order" {
  let path = tmp_test_path("argv_no_warn")
  @fs.write_string_to_file(
    path, "theorem truth_file : ⊢ T := by exact truth\nqed\ntheorem holey : ⊢ T := by hole h1\nqed",
  )
  let result1 = cmd_run_argv(
    ["qed-cmd", "--no-warn", "-d", path],
    default_cmd_options(),
  )
  assert_true(cmd_render_result(result1).contains("ok truth_file: "))
  assert_true(cmd_render_result(result1).contains("warning[unfinished]"))
  assert_eq(cmd_exit_code(result1), 0)
  let result2 = cmd_run_argv(
    ["qed-cmd", "-d", "--no-warn", path],
    default_cmd_options(),
  )
  assert_true(cmd_render_result(result2).contains("ok truth_file: "))
  assert_true(cmd_render_result(result2).contains("warning[unfinished]"))
  assert_eq(cmd_exit_code(result2), 0)
  if @fs.path_exists(path) {
    @fs.remove_file(path)
  }
}
