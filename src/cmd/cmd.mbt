///|
pub struct CmdOptions {
  auto_install_prelude : Bool
  detailed_success : Bool
  no_warn : Bool
}

///|
pub enum CmdFailureKind {
  Usage
  Io
  Parse
  Bridge
  Tactic
  Sig
  Logic
}

///|
pub struct CmdLocalHypSummary {
  name : String
  term_summary : String
}

///|
pub struct CmdSuccess {
  path : String
  theorem_name : String
  conclusion : Term
  conclusion_summary : String
}

///|
pub enum CmdFileItem {
  CmdItemSuccess(CmdSuccess)
  CmdItemFailure(CmdFailure)
  CmdItemWarning(CmdUnfinished)
}

///|
pub struct CmdFileReport {
  path : String
  items : Array[CmdFileItem]
  detailed_success : Bool
  no_warn : Bool
}

///|
pub struct CmdFailure {
  path : String
  theorem_name : String?
  kind : CmdFailureKind
  step_index : Int?
  branch_path : Array[Int]
  current_goal_summary : String?
  local_hyps : Array[CmdLocalHypSummary]
  detail : String
}

///|
pub struct CmdUnfinished {
  path : String
  theorem_name : String
  step_index : Int?
  branch_path : Array[Int]
  current_goal_summary : String
  local_hyps : Array[CmdLocalHypSummary]
  hole_name : String?
  detail : String
}

///|
pub enum CmdRunResult {
  FileReport(CmdFileReport)
  Failure(CmdFailure)
  Unfinished(CmdUnfinished)
}

///|
pub fn default_cmd_options() -> CmdOptions {
  CmdOptions::{
    auto_install_prelude: true,
    detailed_success: false,
    no_warn: false,
  }
}

///|
pub fn cmd_options(auto_install_prelude : Bool) -> CmdOptions {
  CmdOptions::{ auto_install_prelude, detailed_success: false, no_warn: false }
}

///|
pub fn cmd_options_with_detail(
  auto_install_prelude : Bool,
  detailed_success : Bool,
) -> CmdOptions {
  CmdOptions::{ auto_install_prelude, detailed_success, no_warn: false }
}

///|
pub fn cmd_options_full(
  auto_install_prelude : Bool,
  detailed_success : Bool,
  no_warn : Bool,
) -> CmdOptions {
  CmdOptions::{ auto_install_prelude, detailed_success, no_warn }
}

///|
fn cmd_failure(
  path : String,
  theorem_name : String?,
  kind : CmdFailureKind,
  step_index : Int?,
  branch_path : Array[Int],
  current_goal_summary : String?,
  local_hyps : Array[CmdLocalHypSummary],
  detail : String,
) -> CmdRunResult {
  Failure(CmdFailure::{
    path,
    theorem_name,
    kind,
    step_index,
    branch_path,
    current_goal_summary,
    local_hyps,
    detail,
  })
}

///|
pub fn cmd_unfinished(
  path : String,
  theorem_name : String,
  step_index : Int?,
  branch_path : Array[Int],
  current_goal_summary : String,
  local_hyps : Array[CmdLocalHypSummary],
  hole_name : String?,
  detail : String,
) -> CmdRunResult {
  Unfinished(CmdUnfinished::{
    path,
    theorem_name,
    step_index,
    branch_path,
    current_goal_summary,
    local_hyps,
    hole_name,
    detail,
  })
}

///|
fn render_logic_error(err : LogicError) -> String {
  match err {
    TypeMismatch => "TypeMismatch"
    VariableCaptured => "VariableCaptured"
    NotAnEquality => "NotAnEquality"
    NotBoolTerm => "NotBoolTerm"
    AlphaMismatch => "AlphaMismatch"
    InvalidInstantiation => "InvalidInstantiation"
    VarFreeInHyp => "VarFreeInHyp"
    NotTrivialBetaRedex => "NotTrivialBetaRedex"
    BoundaryFailure => "BoundaryFailure"
    CapacityExceeded => "CapacityExceeded"
  }
}

///|
fn cmd_failure_kind_of(kind : ProverDiagnosticKind) -> CmdFailureKind {
  match kind {
    Parse => Parse
    Bridge => Bridge
    Tactic => Tactic
    Sig => Sig
    Logic => Logic
  }
}

///|
fn render_goal_summary(goal : Goal) -> String {
  let hyps = goal_hyps(goal).map(term_to_string).join(", ")
  "[" + hyps + "] |- " + term_to_string(goal_concl(goal))
}

///|
fn summarize_local_hyp(hyp : ProverLocalHyp) -> CmdLocalHypSummary {
  CmdLocalHypSummary::{ name: hyp.name, term_summary: term_to_string(hyp.term) }
}

///|
fn render_local_hyp_summary(local_hyps : Array[CmdLocalHypSummary]) -> String {
  if local_hyps.length() == 0 {
    "<none>"
  } else {
    local_hyps.map(fn(hyp) { hyp.name + ": " + hyp.term_summary }).join(", ")
  }
}

///|
fn usage_string(argv0 : String) -> String {
  "usage: " + argv0 + " [-d] [--no-warn] <file>"
}

///|
fn string_starts_with_dash(s : String) -> Bool {
  match s.view() {
    ['-', ..] => true
    _ => false
  }
}

///|
fn cli_path_label(path : String, theorem_name : String?) -> String {
  match theorem_name {
    Some(name) => path + " (" + name + ")"
    None => path
  }
}

///|
fn cmd_failure_has_context(err : CmdFailure) -> Bool {
  err.step_index is Some(_) ||
  err.branch_path.length() != 0 ||
  err.current_goal_summary is Some(_) ||
  err.local_hyps.length() != 0
}

///|
fn render_branch_path(branch_path : Array[Int]) -> String {
  if branch_path.length() == 0 {
    "<root>"
  } else {
    branch_path.map(fn(idx) { idx.to_string() }).join(".")
  }
}

///|
pub fn cmd_failure_kind_to_string(kind : CmdFailureKind) -> String {
  match kind {
    Usage => "usage"
    Io => "io"
    Parse => "parse"
    Bridge => "bridge"
    Tactic => "tactic"
    Sig => "sig"
    Logic => "logic"
  }
}

///|
pub fn cmd_exit_code(result : CmdRunResult) -> Int {
  match result {
    FileReport(report) => {
      let mut has_warning = false
      for item in report.items {
        match item {
          CmdItemFailure(_) => return 1
          CmdItemWarning(_) => has_warning = true
          CmdItemSuccess(_) => ()
        }
      }
      if has_warning && !report.no_warn {
        1
      } else {
        0
      }
    }
    Failure(_) => 1
    Unfinished(_) => 1
  }
}

///|
fn render_cmd_success(ok : CmdSuccess, detailed_success : Bool) -> String {
  if detailed_success {
    "ok " + ok.theorem_name + ": " + ok.conclusion_summary
  } else {
    "ok " + ok.theorem_name
  }
}

///|
fn render_cmd_failure(err : CmdFailure) -> String {
  let head = "error[" +
    cmd_failure_kind_to_string(err.kind) +
    "] " +
    cli_path_label(err.path, err.theorem_name) +
    ": " +
    err.detail
  if !cmd_failure_has_context(err) {
    head
  } else {
    let lines : Array[String] = [head]
    match err.step_index {
      Some(idx) => lines.push("step: " + idx.to_string())
      None => ()
    }
    if err.branch_path.length() != 0 {
      lines.push("branch: " + render_branch_path(err.branch_path))
    }
    match err.current_goal_summary {
      Some(goal_summary) => lines.push("goal: " + goal_summary)
      None => ()
    }
    lines.push("locals: " + render_local_hyp_summary(err.local_hyps))
    lines.join("\n")
  }
}

///|
fn render_cmd_warning(st : CmdUnfinished) -> String {
  let lines : Array[String] = [
    "warning[unfinished] " +
    cli_path_label(st.path, Some(st.theorem_name)) +
    ": " +
    st.detail,
    "theorem: " + st.theorem_name,
  ]
  let step_summary = match st.step_index {
    Some(idx) => idx.to_string()
    None => "<none>"
  }
  lines.push("step: " + step_summary)
  lines.push("branch: " + render_branch_path(st.branch_path))
  lines.push("goal: " + st.current_goal_summary)
  lines.push("locals: " + render_local_hyp_summary(st.local_hyps))
  match st.hole_name {
    Some(name) => lines.push("hole: " + name)
    None => lines.push("hole: <none>")
  }
  lines.push("message: " + st.detail)
  lines.join("\n")
}

///|
fn render_cmd_unfinished(st : CmdUnfinished) -> String {
  let lines : Array[String] = [
    "unfinished " +
    cli_path_label(st.path, Some(st.theorem_name)) +
    ": " +
    st.detail,
    "theorem: " + st.theorem_name,
  ]
  let step_summary = match st.step_index {
    Some(idx) => idx.to_string()
    None => "<none>"
  }
  lines.push("step: " + step_summary)
  lines.push("branch: " + render_branch_path(st.branch_path))
  lines.push("goal: " + st.current_goal_summary)
  lines.push("locals: " + render_local_hyp_summary(st.local_hyps))
  match st.hole_name {
    Some(name) => lines.push("hole: " + name)
    None => lines.push("hole: <none>")
  }
  lines.push("message: " + st.detail)
  lines.join("\n")
}

///|
pub fn cmd_render_result(result : CmdRunResult) -> String {
  match result {
    FileReport(report) =>
      report.items
      .map(fn(item) {
        match item {
          CmdItemSuccess(success) =>
            render_cmd_success(success, report.detailed_success)
          CmdItemFailure(err) => render_cmd_failure(err)
          CmdItemWarning(st) => render_cmd_warning(st)
        }
      })
      .join("\n")
    Failure(err) => render_cmd_failure(err)
    Unfinished(st) => render_cmd_unfinished(st)
  }
}

///|
fn cmd_success_from_prover(
  path : String,
  ok : ProverSuccess,
) -> Result[CmdSuccess, LogicError] {
  match thm_concl(ok.thm) {
    Err(e) => Err(e)
    Ok(concl) =>
      Ok(CmdSuccess::{
        path,
        theorem_name: ok.theorem_name,
        conclusion: concl,
        conclusion_summary: term_to_string(concl),
      })
  }
}

///|
fn cmd_file_report_from_prover(
  path : String,
  report : ProverFileReport,
  detailed_success : Bool,
  no_warn : Bool,
) -> CmdRunResult {
  let items : Array[CmdFileItem] = []
  for item in report.items {
    match item {
      ProverItemProved(success) =>
        match cmd_success_from_prover(path, success) {
          Ok(cmd_success) => items.push(CmdItemSuccess(cmd_success))
          Err(e) =>
            return cmd_failure(
              path,
              Some(success.theorem_name),
              Logic,
              None,
              [],
              None,
              [],
              render_logic_error(e),
            )
        }
      ProverItemFailed(failure) =>
        match cmd_failure_from_prover(path, failure) {
          Failure(err) => items.push(CmdItemFailure(err))
          _ => panic()
        }
      ProverItemUnfinished(unfinished) =>
        match cmd_unfinished_from_prover(path, unfinished) {
          Unfinished(st) => items.push(CmdItemWarning(st))
          _ => panic()
        }
    }
  }
  FileReport(CmdFileReport::{ path, items, detailed_success, no_warn })
}

///|
fn cmd_failure_from_prover(
  path : String,
  failure : ProverFailure,
) -> CmdRunResult {
  let current_goal_summary = match failure.current_goal {
    Some(goal) => Some(render_goal_summary(goal))
    None => None
  }
  let local_hyps = failure.local_hyps.map(summarize_local_hyp)
  cmd_failure(
    path,
    failure.theorem_name,
    cmd_failure_kind_of(failure.kind),
    failure.step_index,
    failure.branch_path,
    current_goal_summary,
    local_hyps,
    failure.detail,
  )
}

///|
pub fn cmd_unfinished_from_prover(
  path : String,
  unfinished : ProverUnfinished,
) -> CmdRunResult {
  let local_hyps = unfinished.local_hyps.map(summarize_local_hyp)
  cmd_unfinished(
    path,
    unfinished.theorem_name,
    unfinished.step_index,
    unfinished.branch_path,
    render_goal_summary(unfinished.current_goal),
    local_hyps,
    unfinished.hole_name,
    unfinished.detail,
  )
}

///|
pub fn cmd_run_script(
  path : String,
  src : String,
  opts : CmdOptions,
) -> CmdRunResult {
  match
    prove_theorem_file_results_detailed(
      empty_kernel_state(),
      src,
      prover_options(opts.auto_install_prelude),
    ) {
    FileChecked(report) =>
      cmd_file_report_from_prover(
        path,
        report,
        opts.detailed_success,
        opts.no_warn,
      )
    FileFailed(failure) => cmd_failure_from_prover(path, failure)
  }
}

///|
pub fn cmd_run_argv(args : Array[String], opts : CmdOptions) -> CmdRunResult {
  let argv0 = if args.length() > 0 { args[0] } else { "qed-cmd" }
  let mut detailed_success = opts.detailed_success
  let mut no_warn = opts.no_warn
  let mut path : String? = None
  let mut i = 1
  while i < args.length() {
    let arg = args[i]
    if arg == "-d" {
      detailed_success = true
    } else if arg == "--no-warn" {
      no_warn = true
    } else if string_starts_with_dash(arg) {
      return cmd_failure(
        "<cli>",
        None,
        Usage,
        None,
        [],
        None,
        [],
        usage_string(argv0),
      )
    } else {
      match path {
        None => path = Some(arg)
        Some(_) =>
          return cmd_failure(
            "<cli>",
            None,
            Usage,
            None,
            [],
            None,
            [],
            usage_string(argv0),
          )
      }
    }
    i = i + 1
  }
  let path = match path {
    Some(v) => v
    None =>
      return cmd_failure(
        "<cli>",
        None,
        Usage,
        None,
        [],
        None,
        [],
        usage_string(argv0),
      )
  }
  let opts2 = cmd_options_full(
    opts.auto_install_prelude,
    detailed_success,
    no_warn,
  )
  let mut src = ""
  try read_file_to_string(path) catch {
    IOError(msg) => return cmd_failure(path, None, Io, None, [], None, [], msg)
  } noraise {
    content => src = content
  }
  cmd_run_script(path, src, opts2)
}

///|
fn main {
  let result = cmd_run_argv(@env.args(), default_cmd_options())
  println(cmd_render_result(result))
  let code = cmd_exit_code(result)
  if code != 0 {
    exit(code)
  }
}
