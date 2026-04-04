///|
pub struct ProverOptions {
  auto_install_prelude : Bool
}

///|
pub enum ProverError {
  Parse(ParseError)
  Bridge(ParseBridgeError)
  Tactic(TacticExecError)
  Sig(SigError)
  Logic(LogicError)
}

///|
pub enum ProverDiagnosticKind {
  Parse
  Bridge
  Tactic
  Sig
  Logic
}

///|
pub struct ProverLocalHyp {
  name : String
  term : Term
}

///|
pub struct ProverSuccess {
  state : KernelState
  theorem_name : String
  thm : Thm
}

///|
pub struct ProverFailure {
  theorem_name : String?
  kind : ProverDiagnosticKind
  detail : String
  raw_offset : Int?
  goal_src : String?
  goal_span : SourceSpan?
  step_index : Int?
  step_span : SourceSpan?
  step_src : String?
  current_goal : Goal?
  local_hyps : Array[ProverLocalHyp]
  error : ProverError
}

///|
pub enum ProverRunResult {
  Proved(ProverSuccess)
  Failed(ProverFailure)
}

///|
pub fn default_prover_options() -> ProverOptions {
  ProverOptions::{ auto_install_prelude: true }
}

///|
pub fn prover_options(auto_install_prelude : Bool) -> ProverOptions {
  ProverOptions::{ auto_install_prelude, }
}

///|
fn step_from_syn(step : SynTacticStep) -> TacticStep {
  match step {
    Intro(n) => step_intro(n)
    Exact(n) => step_exact(n)
    Apply(n) => step_apply(n)
    Assumption => step_assumption()
    Split => step_split()
    Left => step_left()
    Right => step_right()
  }
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
fn render_bridge_error(err : ParseBridgeError) -> String {
  match err {
    Parse(e) => "Parse(" + render_parse_error(e) + ")"
    Sig(e) => "Sig(" + render_sig_error(e) + ")"
    Logic(e) => "Logic(" + render_logic_error(e) + ")"
    Elab(e) => "Elab(" + render_elab_error(e) + ")"
  }
}

///|
fn diagnostic_kind(error : ProverError) -> ProverDiagnosticKind {
  match error {
    Parse(_) => Parse
    Bridge(_) => Bridge
    Tactic(_) => Tactic
    Sig(_) => Sig
    Logic(_) => Logic
  }
}

///|
fn diagnostic_detail(error : ProverError) -> String {
  match error {
    Parse(e) => render_parse_error(e)
    Bridge(e) => render_bridge_error(e)
    Tactic(e) => render_tactic_error(e)
    Sig(e) => render_sig_error(e)
    Logic(e) => render_logic_error(e)
  }
}

///|
fn prover_failure(
  theorem_name : String?,
  goal_src : String?,
  goal_span : SourceSpan?,
  step_index : Int?,
  step_span : SourceSpan?,
  step_src : String?,
  current_goal : Goal?,
  local_hyps : Array[ProverLocalHyp],
  error : ProverError,
  raw_offset : Int?,
) -> ProverRunResult {
  Failed(ProverFailure::{
    theorem_name,
    kind: diagnostic_kind(error),
    detail: diagnostic_detail(error),
    raw_offset,
    goal_src,
    goal_span,
    step_index,
    step_span,
    step_src,
    current_goal,
    local_hyps,
    error,
  })
}

///|
fn prover_local_hyps_of(ps : ProofState) -> Array[ProverLocalHyp] {
  ps_current_local_hyps(ps).map(fn(hyp) {
    ProverLocalHyp::{ name: local_hyp_name(hyp), term: local_hyp_term(hyp) }
  })
}

///|
pub fn prove_theorem_script_detailed(
  state : KernelState,
  src : String,
  opts : ProverOptions,
) -> ProverRunResult {
  let st1 = if opts.auto_install_prelude {
    match install_prop_prelude(state) {
      Ok(v) => v
      Err(e) =>
        return prover_failure(
          None,
          None,
          None,
          None,
          None,
          None,
          None,
          [],
          Sig(e),
          None,
        )
    }
  } else {
    state
  }
  let prelude = default_prop_prelude()
  let syn = match parse_theorem_script_raw(src) {
    Ok(v) => v
    Err(e) =>
      return prover_failure(
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        [],
        Parse(e),
        Some(e.offset),
      )
  }
  let goal = match lower_syn_goal_with_env(st1, empty_parse_env(), syn.goal) {
    Ok(v) => v
    Err(e) =>
      match e {
        Sig(sig_e) =>
          return prover_failure(
            Some(syn.name),
            Some(syn.goal_src),
            Some(syn.goal_span),
            None,
            None,
            None,
            None,
            [],
            Sig(sig_e),
            Some(syn.goal_span.start_offset),
          )
        Logic(logic_e) =>
          return prover_failure(
            Some(syn.name),
            Some(syn.goal_src),
            Some(syn.goal_span),
            None,
            None,
            None,
            None,
            [],
            Logic(logic_e),
            Some(syn.goal_span.start_offset),
          )
        _ =>
          return prover_failure(
            Some(syn.name),
            Some(syn.goal_src),
            Some(syn.goal_span),
            None,
            None,
            None,
            None,
            [],
            Bridge(e),
            Some(syn.goal_span.start_offset),
          )
      }
  }
  let mut ps = ps_init(goal)
  let mut i = 0
  while i < syn.body.steps.length() {
    let script_step = syn.body.steps[i]
    let current_goal = ps_current_goal(ps)
    let local_hyps = prover_local_hyps_of(ps)
    let step = step_from_syn(script_step.step)
    ps = match ps_apply(st1, prelude, ps, step) {
      Ok(v) => v
      Err(e) =>
        return prover_failure(
          Some(syn.name),
          Some(syn.goal_src),
          Some(syn.goal_span),
          Some(i + 1),
          Some(script_step.span),
          Some(script_step.src),
          current_goal,
          local_hyps,
          Tactic(e),
          Some(script_step.span.start_offset),
        )
    }
    i = i + 1
  }
  let current_goal = ps_current_goal(ps)
  let local_hyps = prover_local_hyps_of(ps)
  match ps_qed(ps) {
    Ok(th) =>
      Proved(ProverSuccess::{ state: st1, theorem_name: syn.name, thm: th })
    Err(e) =>
      prover_failure(
        Some(syn.name),
        Some(syn.goal_src),
        Some(syn.goal_span),
        None,
        None,
        None,
        current_goal,
        local_hyps,
        Tactic(e),
        None,
      )
  }
}

///|
pub fn prove_theorem_script_with_diagnostics(
  state : KernelState,
  src : String,
  opts : ProverOptions,
) -> Result[(KernelState, Thm), ProverFailure] {
  match prove_theorem_script_detailed(state, src, opts) {
    Proved(ok) => Ok((ok.state, ok.thm))
    Failed(err) => Err(err)
  }
}

///|
pub fn prove_theorem_script(
  state : KernelState,
  src : String,
  opts : ProverOptions,
) -> Result[(KernelState, Thm), ProverError] {
  match prove_theorem_script_detailed(state, src, opts) {
    Proved(ok) => Ok((ok.state, ok.thm))
    Failed(err) => Err(err.error)
  }
}
