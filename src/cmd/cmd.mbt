///|
pub struct CmdOptions {
  auto_install_prelude : Bool
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
pub struct CmdFailure {
  path : String
  theorem_name : String?
  kind : CmdFailureKind
  step_index : Int?
  current_goal_summary : String?
  local_hyps : Array[CmdLocalHypSummary]
  detail : String
}

///|
pub enum CmdRunResult {
  Success(CmdSuccess)
  Failure(CmdFailure)
}

///|
pub fn default_cmd_options() -> CmdOptions {
  CmdOptions::{ auto_install_prelude: true }
}

///|
pub fn cmd_options(auto_install_prelude : Bool) -> CmdOptions {
  CmdOptions::{ auto_install_prelude, }
}

///|
fn cmd_failure(
  path : String,
  theorem_name : String?,
  kind : CmdFailureKind,
  step_index : Int?,
  current_goal_summary : String?,
  local_hyps : Array[CmdLocalHypSummary],
  detail : String,
) -> CmdRunResult {
  Failure(CmdFailure::{
    path,
    theorem_name,
    kind,
    step_index,
    current_goal_summary,
    local_hyps,
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
fn render_sig_error(err : SigError) -> String {
  match err {
    DuplicateConstName => "DuplicateConstName"
    ConstTypeConflict => "ConstTypeConflict"
    InvalidConstInstance => "InvalidConstInstance"
    UnknownConst => "UnknownConst"
    ScopeUnderflow => "ScopeUnderflow"
    InvalidConstRhs => "InvalidConstRhs"
    ReservedSymbol => "ReservedSymbol"
    DefinitionAlreadyExists => "DefinitionAlreadyExists"
    DefinitionNotClosed => "DefinitionNotClosed"
    DefinitionIsCyclic => "DefinitionIsCyclic"
    GhostTypeVariable => "GhostTypeVariable"
    InvalidTypeWitness => "InvalidTypeWitness"
    InvalidTypePredicate => "InvalidTypePredicate"
    InvalidTypeRepName => "InvalidTypeRepName"
    InvalidTypeAbsName => "InvalidTypeAbsName"
    InvalidTypeParams => "InvalidTypeParams"
    InvalidTypeArity => "InvalidTypeArity"
    TypeWitnessArityMismatch => "TypeWitnessArityMismatch"
    TypeWitnessPredicateMismatch => "TypeWitnessPredicateMismatch"
    TypeConstructorAlreadyExists => "TypeConstructorAlreadyExists"
    TypeRepresentationAlreadyExists => "TypeRepresentationAlreadyExists"
    TypeAbstractionAlreadyExists => "TypeAbstractionAlreadyExists"
    InvalidInfinityAnchor => "InvalidInfinityAnchor"
    MissingInfinityAnchor => "MissingInfinityAnchor"
    InvalidTypeDefinitionProduct => "InvalidTypeDefinitionProduct"
    MissingTypeDefinitionContract => "MissingTypeDefinitionContract"
    InvalidSpecificationWitness => "InvalidSpecificationWitness"
    InvalidSpecificationPredicate => "InvalidSpecificationPredicate"
    SpecificationTypeVarLeak => "SpecificationTypeVarLeak"
    TypeMismatch => "TypeMismatch"
  }
}

///|
fn render_elab_error(err : ElabError) -> String {
  match err {
    UnknownName(name) => "UnknownName(" + name + ")"
    UnknownConst(name) => "UnknownConst(" + name + ")"
    InvalidConstInstance(name) => "InvalidConstInstance(" + name + ")"
    ScopeResolutionMismatch => "ScopeResolutionMismatch"
    CoreTypingFailure => "CoreTypingFailure"
  }
}

///|
fn render_tactic_error(err : TacticExecError) -> String {
  match err {
    UnknownName(name) => "UnknownName(" + name + ")"
    GoalShapeMismatch(msg) => "GoalShapeMismatch(" + msg + ")"
    ApplyMismatch(msg) => "ApplyMismatch(" + msg + ")"
    NoGoals => "NoGoals"
    UnsolvedGoals => "UnsolvedGoals"
    ProofSynthesisUnavailable(msg) => "ProofSynthesisUnavailable(" + msg + ")"
    Logic(e) => "Logic(" + render_logic_error(e) + ")"
  }
}

///|
fn render_parse_error(err : ParseError) -> String {
  "offset " + err.offset.to_string() + ": " + err.detail
}

///|
fn render_bridge_error(err : ParseBridgeError) -> String {
  match err {
    Parse(e) => "Parse(" + render_parse_error(e) + ")"
    Sig(e) => "Sig(" + render_sig_error(e) + ")"
    Logic(e) => "Logic(" + render_logic_error(e) + ")"
    Elab(e) => "Elab(" + render_elab_error(e) + ")"
  }
}

///|
fn prover_error_failure(err : ProverError) -> (CmdFailureKind, String) {
  match err {
    Parse(e) => (Parse, render_parse_error(e))
    Bridge(e) => (Bridge, render_bridge_error(e))
    Tactic(e) => (Tactic, render_tactic_error(e))
    Sig(e) => (Sig, render_sig_error(e))
    Logic(e) => (Logic, render_logic_error(e))
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
  "usage: " + argv0 + " <file>"
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
  err.current_goal_summary is Some(_) ||
  err.local_hyps.length() != 0
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
    Success(_) => 0
    Failure(_) => 1
  }
}

///|
pub fn cmd_render_result(result : CmdRunResult) -> String {
  match result {
    Success(ok) => "ok " + ok.theorem_name + ": " + ok.conclusion_summary
    Failure(err) => {
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
        match err.current_goal_summary {
          Some(goal_summary) => lines.push("goal: " + goal_summary)
          None => ()
        }
        lines.push("locals: " + render_local_hyp_summary(err.local_hyps))
        lines.join("\n")
      }
    }
  }
}

///|
fn cmd_failure_from_prover(
  path : String,
  failure : ProverFailure,
) -> CmdRunResult {
  let (kind, detail) = prover_error_failure(failure.error)
  let current_goal_summary = match failure.current_goal {
    Some(goal) => Some(render_goal_summary(goal))
    None => None
  }
  let local_hyps = failure.local_hyps.map(summarize_local_hyp)
  cmd_failure(
    path,
    failure.theorem_name,
    kind,
    failure.step_index,
    current_goal_summary,
    local_hyps,
    detail,
  )
}

///|
pub fn cmd_run_script(
  path : String,
  src : String,
  opts : CmdOptions,
) -> CmdRunResult {
  match parse_theorem_script_raw(src) {
    Err(e) =>
      cmd_failure(path, None, Parse, None, None, [], render_parse_error(e))
    Ok(script) =>
      match
        prove_theorem_script_detailed(
          empty_kernel_state(),
          src,
          prover_options(opts.auto_install_prelude),
        ) {
        Proved(ok) =>
          match thm_concl(ok.thm) {
            Err(e) =>
              cmd_failure(
                path,
                Some(script.name),
                Logic,
                None,
                None,
                [],
                render_logic_error(e),
              )
            Ok(concl) =>
              Success(CmdSuccess::{
                path,
                theorem_name: ok.theorem_name,
                conclusion: concl,
                conclusion_summary: term_to_string(concl),
              })
          }
        Failed(failure) => cmd_failure_from_prover(path, failure)
      }
  }
}

///|
pub fn cmd_run_argv(args : Array[String], opts : CmdOptions) -> CmdRunResult {
  let argv0 = if args.length() > 0 { args[0] } else { "qed-cmd" }
  if args.length() != 2 {
    return cmd_failure(
      "<cli>",
      None,
      Usage,
      None,
      None,
      [],
      usage_string(argv0),
    )
  }
  let path = args[1]
  let mut src = ""
  try read_file_to_string(path) catch {
    IOError(msg) => return cmd_failure(path, None, Io, None, None, [], msg)
  } noraise {
    content => src = content
  }
  cmd_run_script(path, src, opts)
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
