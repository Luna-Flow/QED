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
pub fn prover_local_hyp(name : String, term : Term) -> ProverLocalHyp {
  ProverLocalHyp::{ name, term }
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
  branch_path : Array[Int]
  step_span : SourceSpan?
  step_src : String?
  current_goal : Goal?
  local_hyps : Array[ProverLocalHyp]
  error : ProverError
}

///|
pub enum ProverScriptError {
  Failure(ProverFailure)
  Unfinished(ProverUnfinished)
}

///|
pub struct ProverUnfinished {
  theorem_name : String
  detail : String
  raw_offset : Int?
  goal_src : String?
  goal_span : SourceSpan?
  step_index : Int?
  branch_path : Array[Int]
  step_span : SourceSpan?
  step_src : String?
  current_goal : Goal
  local_hyps : Array[ProverLocalHyp]
  hole_name : String?
}

///|
pub enum ProverRunResult {
  Proved(ProverSuccess)
  Failed(ProverFailure)
  Unfinished(ProverUnfinished)
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
    Hole(_) => panic()
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
  branch_path : Array[Int],
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
    branch_path,
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
pub fn prover_unfinished(
  theorem_name : String,
  goal_src : String?,
  goal_span : SourceSpan?,
  step_index : Int?,
  branch_path : Array[Int],
  step_span : SourceSpan?,
  step_src : String?,
  current_goal : Goal,
  local_hyps : Array[ProverLocalHyp],
  hole_name : String?,
  detail : String,
  raw_offset : Int?,
) -> ProverRunResult {
  Unfinished(ProverUnfinished::{
    theorem_name,
    detail,
    raw_offset,
    goal_src,
    goal_span,
    step_index,
    branch_path,
    step_span,
    step_src,
    current_goal,
    local_hyps,
    hole_name,
  })
}

///|
fn goal_shape_matches(state : KernelState, lhs : Goal, rhs : Goal) -> Bool {
  let nf_term = fn(term : Term) {
    match logic_beta_nf_bool_term_deep(state, term) {
      Ok(v) => v
      Err(_) => term
    }
  }
  let lhs_hyps = goal_hyps(lhs)
  let rhs_hyps = goal_hyps(rhs)
  if lhs_hyps.length() != rhs_hyps.length() {
    return false
  }
  let used : Array[Bool] = []
  let mut i = 0
  while i < rhs_hyps.length() {
    used.push(false)
    i = i + 1
  }
  for h in lhs_hyps {
    let h_nf = nf_term(h)
    let mut j = 0
    let mut matched = false
    while j < rhs_hyps.length() {
      let rhs_nf = nf_term(rhs_hyps[j])
      if !used[j] &&
        (term_logical_eq(h_nf, rhs_nf) || term_alpha_eq(h_nf, rhs_nf)) {
        used[j] = true
        matched = true
        break
      }
      j = j + 1
    }
    if !matched {
      return false
    }
  }
  let lhs_concl = nf_term(goal_concl(lhs))
  let rhs_concl = nf_term(goal_concl(rhs))
  term_logical_eq(lhs_concl, rhs_concl) || term_alpha_eq(lhs_concl, rhs_concl)
}

///|
fn step_branch_arity(step : SynTacticStep) -> Int {
  match step {
    Split => 2
    Left => 1
    Right => 1
    _ => 0
  }
}

///|
fn branch_step_failure(
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  step_index : Int,
  branch_path : Array[Int],
  script_step : SynScriptStep,
  current_goal : Goal?,
  local_hyps : Array[ProverLocalHyp],
  error : ProverError,
  raw_offset : Int?,
) -> ProverRunResult {
  prover_failure(
    Some(theorem_name),
    Some(goal_src),
    Some(goal_span),
    Some(step_index),
    branch_path,
    Some(script_step.span),
    Some(script_step.src),
    current_goal,
    local_hyps,
    error,
    raw_offset,
  )
}

///|
fn branch_goal_failure(
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  step_index : Int,
  branch_path : Array[Int],
  script_step : SynScriptStep,
  ps : ProofState,
  detail : String,
  raw_offset : Int?,
) -> ProverRunResult {
  branch_step_failure(
    theorem_name,
    goal_src,
    goal_span,
    step_index,
    branch_path,
    script_step,
    ps_current_goal(ps),
    prover_local_hyps_of(ps),
    Tactic(tactic_goal_shape_mismatch(detail)),
    raw_offset,
  )
}

///|
fn structured_branch_step_result(
  state : KernelState,
  prelude : PropPrelude,
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  _before_step : ProofState,
  after_step : ProofState,
  script_step : SynScriptStep,
  step_idx : Int,
  branch_path : Array[Int],
  before_goal_count : Int,
) -> (ProofState, Int, ProverRunResult?) {
  let branch_arity = step_branch_arity(script_step.step)
  if script_step.branches.length() != 0 &&
    script_step.branches.length() != branch_arity {
    return (
      after_step,
      step_idx,
      Some(
        branch_step_failure(
          theorem_name,
          goal_src,
          goal_span,
          step_idx,
          branch_path,
          script_step,
          ps_current_goal(after_step),
          prover_local_hyps_of(after_step),
          Tactic(
            tactic_goal_shape_mismatch(
              "structured branch count does not match tactic",
            ),
          ),
          Some(script_step.span.start_offset),
        ),
      ),
    )
  }
  if script_step.branches.length() == 0 {
    return (after_step, step_idx, None)
  }

  let after_step_goal_count = ps_goal_count(after_step)
  match script_step.step {
    Split => {
      if after_step_goal_count != before_goal_count + 1 {
        return (
          after_step,
          step_idx,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              step_idx,
              branch_path,
              script_step,
              ps_current_goal(after_step),
              prover_local_hyps_of(after_step),
              Tactic(
                tactic_goal_shape_mismatch(
                  "split did not create the expected branch goal count",
                ),
              ),
              Some(script_step.span.start_offset),
            ),
          ),
        )
      }
      let (next_ps, next_step_idx, err) = run_split_branch_bodies(
        state, prelude, theorem_name, goal_src, goal_span, after_step, script_step,
        step_idx, before_goal_count, branch_path,
      )
      match err {
        Some(v) => (next_ps, next_step_idx, Some(v))
        None => (next_ps, next_step_idx, None)
      }
    }
    Left | Right => {
      if after_step_goal_count != before_goal_count {
        return (
          after_step,
          step_idx,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              step_idx,
              branch_path,
              script_step,
              ps_current_goal(after_step),
              prover_local_hyps_of(after_step),
              Tactic(
                tactic_goal_shape_mismatch(
                  "disjunction branch did not preserve expected goal count",
                ),
              ),
              Some(script_step.span.start_offset),
            ),
          ),
        )
      }
      let (next_ps, next_step_idx, err) = run_disjunction_branch_body(
        state, prelude, theorem_name, goal_src, goal_span, after_step, script_step,
        step_idx, before_goal_count, branch_path,
      )
      match err {
        Some(v) => (next_ps, next_step_idx, Some(v))
        None => (next_ps, next_step_idx, None)
      }
    }
    _ => (after_step, step_idx, None)
  }
}

///|
fn run_split_branch_bodies(
  state : KernelState,
  prelude : PropPrelude,
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  ps : ProofState,
  script_step : SynScriptStep,
  step_idx : Int,
  before_goal_count : Int,
  branch_path : Array[Int],
) -> (ProofState, Int, ProverRunResult?) {
  let branch1_goal = match ps_pending_goal_at(ps, 0) {
    Some(goal) => goal
    None =>
      return (
        ps,
        step_idx,
        Some(
          branch_goal_failure(
            theorem_name,
            goal_src,
            goal_span,
            step_idx,
            branch_path,
            script_step,
            ps,
            "split did not expose the first branch goal",
            Some(script_step.span.start_offset),
          ),
        ),
      )
  }
  let branch2_goal = match ps_pending_goal_at(ps, 1) {
    Some(goal) => goal
    None =>
      return (
        ps,
        step_idx,
        Some(
          branch_goal_failure(
            theorem_name,
            goal_src,
            goal_span,
            step_idx,
            branch_path,
            script_step,
            ps,
            "split did not expose the second branch goal",
            Some(script_step.span.start_offset),
          ),
        ),
      )
  }
  match ps_current_goal(ps) {
    Some(goal) =>
      if !goal_shape_matches(state, goal, branch1_goal) {
        let branch1_path = branch_path.copy()
        branch1_path.push(1)
        return (
          ps,
          step_idx,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              step_idx,
              branch1_path,
              script_step,
              Some(goal),
              prover_local_hyps_of(ps),
              Tactic(
                tactic_goal_shape_mismatch(
                  "first split branch body did not start from the first split goal",
                ),
              ),
              Some(script_step.branches[0].span.start_offset),
            ),
          ),
        )
      }
    None => {
      let branch1_path = branch_path.copy()
      branch1_path.push(1)
      return (
        ps,
        step_idx,
        Some(
          branch_step_failure(
            theorem_name,
            goal_src,
            goal_span,
            step_idx,
            branch1_path,
            script_step,
            None,
            prover_local_hyps_of(ps),
            Tactic(
              tactic_goal_shape_mismatch(
                "first split branch body did not start from the first split goal",
              ),
            ),
            Some(script_step.branches[0].span.start_offset),
          ),
        ),
      )
    }
  }
  let branch1_path = branch_path.copy()
  branch1_path.push(1)
  let (after_branch1, next_idx1, err1) = execute_script_body(
    state,
    prelude,
    theorem_name,
    goal_src,
    goal_span,
    ps,
    script_step.branches[0].body,
    step_idx,
    branch1_path,
    0,
  )
  match err1 {
    Some(v) => return (after_branch1, next_idx1, Some(v))
    None => ()
  }
  if ps_goal_count(after_branch1) != before_goal_count {
    return (
      after_branch1,
      next_idx1,
      Some(
        branch_step_failure(
          theorem_name,
          goal_src,
          goal_span,
          next_idx1,
          branch1_path,
          script_step,
          ps_current_goal(after_branch1),
          prover_local_hyps_of(after_branch1),
          Tactic(
            tactic_goal_shape_mismatch(
              "first split branch did not discharge exactly one branch goal",
            ),
          ),
          Some(script_step.branches[0].span.start_offset),
        ),
      ),
    )
  }
  match ps_current_goal(after_branch1) {
    Some(goal) =>
      if !goal_shape_matches(state, goal, branch2_goal) {
        return (
          after_branch1,
          next_idx1,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              next_idx1,
              branch_path,
              script_step,
              Some(goal),
              prover_local_hyps_of(after_branch1),
              Tactic(
                tactic_goal_shape_mismatch(
                  "split branch order does not match the explicit branch bodies",
                ),
              ),
              Some(script_step.branches[1].span.start_offset),
            ),
          ),
        )
      }
    None =>
      return (
        after_branch1,
        next_idx1,
        Some(
          branch_step_failure(
            theorem_name,
            goal_src,
            goal_span,
            next_idx1,
            branch_path,
            script_step,
            None,
            prover_local_hyps_of(after_branch1),
            Tactic(
              tactic_goal_shape_mismatch(
                "split branch order does not match the explicit branch bodies",
              ),
            ),
            Some(script_step.branches[1].span.start_offset),
          ),
        ),
      )
  }
  let branch2_path = branch_path.copy()
  branch2_path.push(2)
  let (after_branch2, next_idx2, err2) = execute_script_body(
    state,
    prelude,
    theorem_name,
    goal_src,
    goal_span,
    after_branch1,
    script_step.branches[1].body,
    next_idx1,
    branch2_path,
    0,
  )
  match err2 {
    Some(v) => return (after_branch2, next_idx2, Some(v))
    None => ()
  }
  if ps_goal_count(after_branch2) != before_goal_count - 1 {
    return (
      after_branch2,
      next_idx2,
      Some(
        branch_step_failure(
          theorem_name,
          goal_src,
          goal_span,
          next_idx2,
          branch2_path,
          script_step,
          ps_current_goal(after_branch2),
          prover_local_hyps_of(after_branch2),
          Tactic(
            tactic_goal_shape_mismatch(
              "split branch blocks did not fully discharge conjunction goal",
            ),
          ),
          Some(script_step.branches[1].span.start_offset),
        ),
      ),
    )
  }
  (after_branch2, next_idx2, None)
}

///|
fn run_disjunction_branch_body(
  state : KernelState,
  prelude : PropPrelude,
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  ps : ProofState,
  script_step : SynScriptStep,
  step_idx : Int,
  before_goal_count : Int,
  branch_path : Array[Int],
) -> (ProofState, Int, ProverRunResult?) {
  let branch_goal = match ps_pending_goal_at(ps, 0) {
    Some(goal) => goal
    None =>
      return (
        ps,
        step_idx,
        Some(
          branch_goal_failure(
            theorem_name,
            goal_src,
            goal_span,
            step_idx,
            branch_path,
            script_step,
            ps,
            "disjunction branch did not expose the selected branch goal",
            Some(script_step.span.start_offset),
          ),
        ),
      )
  }
  match ps_current_goal(ps) {
    Some(goal) =>
      if !goal_shape_matches(state, goal, branch_goal) {
        let branch1_path = branch_path.copy()
        branch1_path.push(1)
        return (
          ps,
          step_idx,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              step_idx,
              branch1_path,
              script_step,
              Some(goal),
              prover_local_hyps_of(ps),
              Tactic(
                tactic_goal_shape_mismatch(
                  "disjunction branch body did not start from the selected branch goal",
                ),
              ),
              Some(script_step.branches[0].span.start_offset),
            ),
          ),
        )
      }
    None => {
      let branch1_path = branch_path.copy()
      branch1_path.push(1)
      return (
        ps,
        step_idx,
        Some(
          branch_step_failure(
            theorem_name,
            goal_src,
            goal_span,
            step_idx,
            branch1_path,
            script_step,
            None,
            prover_local_hyps_of(ps),
            Tactic(
              tactic_goal_shape_mismatch(
                "disjunction branch body did not start from the selected branch goal",
              ),
            ),
            Some(script_step.branches[0].span.start_offset),
          ),
        ),
      )
    }
  }
  let branch1_path = branch_path.copy()
  branch1_path.push(1)
  let (after_branch, next_idx, err) = execute_script_body(
    state,
    prelude,
    theorem_name,
    goal_src,
    goal_span,
    ps,
    script_step.branches[0].body,
    step_idx,
    branch1_path,
    0,
  )
  match err {
    Some(v) => return (after_branch, next_idx, Some(v))
    None => ()
  }
  if ps_goal_count(after_branch) != before_goal_count - 1 {
    return (
      after_branch,
      next_idx,
      Some(
        branch_step_failure(
          theorem_name,
          goal_src,
          goal_span,
          next_idx,
          branch1_path,
          script_step,
          ps_current_goal(after_branch),
          prover_local_hyps_of(after_branch),
          Tactic(
            tactic_goal_shape_mismatch(
              "branch block did not fully discharge disjunction branch goal",
            ),
          ),
          Some(script_step.branches[0].span.start_offset),
        ),
      ),
    )
  }
  (after_branch, next_idx, None)
}

///|
fn execute_script_body(
  state : KernelState,
  prelude : PropPrelude,
  theorem_name : String,
  goal_src : String,
  goal_span : SourceSpan,
  ps : ProofState,
  body : SynScriptBody,
  next_step_index : Int,
  branch_path : Array[Int],
  skip_prefix_steps : Int,
) -> (ProofState, Int, ProverRunResult?) {
  let mut out = ps
  let mut step_idx = next_step_index
  let mut body_idx = 0
  for script_step in body.steps {
    if body_idx < skip_prefix_steps {
      body_idx = body_idx + 1
      continue
    }
    body_idx = body_idx + 1
    let before_step = out
    step_idx = step_idx + 1
    let current_goal = ps_current_goal(before_step)
    let local_hyps = prover_local_hyps_of(before_step)
    match script_step.step {
      Hole(name) =>
        match current_goal {
          Some(goal) =>
            return (
              before_step,
              step_idx,
              Some(
                prover_unfinished(
                  theorem_name,
                  Some(goal_src),
                  Some(goal_span),
                  Some(step_idx),
                  branch_path,
                  Some(script_step.span),
                  Some(script_step.src),
                  goal,
                  local_hyps,
                  name,
                  "proof contains an unfinished hole",
                  Some(script_step.span.start_offset),
                ),
              ),
            )
          None =>
            return (
              before_step,
              step_idx,
              Some(
                branch_step_failure(
                  theorem_name,
                  goal_src,
                  goal_span,
                  step_idx,
                  branch_path,
                  script_step,
                  current_goal,
                  local_hyps,
                  Tactic(
                    tactic_goal_shape_mismatch(
                      "hole step encountered after all goals were already discharged",
                    ),
                  ),
                  Some(script_step.span.start_offset),
                ),
              ),
            )
        }
      _ => ()
    }
    let step = step_from_syn(script_step.step)
    out = match ps_apply(state, prelude, before_step, step) {
      Ok(v) => v
      Err(e) =>
        return (
          before_step,
          step_idx,
          Some(
            branch_step_failure(
              theorem_name,
              goal_src,
              goal_span,
              step_idx,
              branch_path,
              script_step,
              current_goal,
              local_hyps,
              Tactic(e),
              Some(script_step.span.start_offset),
            ),
          ),
        )
    }
    let before_goal_count = ps_goal_count(before_step)
    let (next_ps, next_step_idx, err) = structured_branch_step_result(
      state, prelude, theorem_name, goal_src, goal_span, before_step, out, script_step,
      step_idx, branch_path, before_goal_count,
    )
    out = next_ps
    step_idx = next_step_idx
    match err {
      Some(v) => return (out, step_idx, Some(v))
      None => continue
    }
  }
  (out, step_idx, None)
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
          [],
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
        [],
        None,
        None,
        None,
        [],
        Parse(e),
        Some(e.offset),
      )
  }
  let mut goal_env = empty_parse_env()
  for binder in syn.binders {
    goal_env = parse_env_push_local(goal_env, binder.name, binder.ty)
  }
  let goal = match lower_syn_goal_with_env(st1, goal_env, syn.goal) {
    Ok(v) => mk_goal(parsed_goal_hyps(v), parsed_goal_concl(v))
    Err(e) =>
      match e {
        Sig(sig_e) =>
          return prover_failure(
            Some(syn.name),
            Some(syn.goal_src),
            Some(syn.goal_span),
            None,
            [],
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
            [],
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
            [],
            None,
            None,
            None,
            [],
            Bridge(e),
            Some(syn.goal_span.start_offset),
          )
      }
  }
  let ps0 = ps_init(goal)
  let (ps, _, exec_err) = execute_script_body(
    st1,
    prelude,
    syn.name,
    syn.goal_src,
    syn.goal_span,
    ps0,
    syn.body,
    0,
    [],
    0,
  )
  match exec_err {
    Some(v) => return v
    None => ()
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
        ps_current_branch_path(ps),
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
) -> Result[(KernelState, Thm), ProverScriptError] {
  match prove_theorem_script_detailed(state, src, opts) {
    Proved(ok) => Ok((ok.state, ok.thm))
    Failed(err) => Err(Failure(err))
    Unfinished(unfinished) => Err(Unfinished(unfinished))
  }
}

///|
pub fn prove_theorem_script(
  state : KernelState,
  src : String,
  opts : ProverOptions,
) -> Result[(KernelState, Thm), ProverScriptError] {
  match prove_theorem_script_detailed(state, src, opts) {
    Proved(ok) => Ok((ok.state, ok.thm))
    Failed(err) => Err(Failure(err))
    Unfinished(unfinished) => Err(Unfinished(unfinished))
  }
}
