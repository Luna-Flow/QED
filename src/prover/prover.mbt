///|
using @kernel {type KernelState, type Thm, type SigError, type LogicError}

///|
using @parser {
  type ParseError,
  type ParseBridgeError,
  type SynTacticStep,
  empty_parse_env,
  parse_theorem_script_raw,
  lower_syn_goal_with_env,
}

///|
using @tactics {
  type TacticStep,
  type TacticExecError,
  ps_init,
  ps_apply_script,
  ps_qed,
  step_intro,
  step_exact,
  step_apply,
  step_assumption,
  step_split,
  step_left,
  step_right,
}

///|
using @logic {install_prop_prelude, default_prop_prelude}

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
pub fn prove_theorem_script(
  state : KernelState,
  src : String,
  opts : ProverOptions,
) -> Result[(KernelState, Thm), ProverError] {
  let st1 = if opts.auto_install_prelude {
    match install_prop_prelude(state) {
      Ok(v) => v
      Err(e) => return Err(Sig(e))
    }
  } else {
    state
  }
  let prelude = default_prop_prelude()
  let syn = match parse_theorem_script_raw(src) {
    Ok(v) => v
    Err(e) => return Err(Parse(e))
  }
  let goal = match lower_syn_goal_with_env(st1, empty_parse_env(), syn.goal) {
    Ok(v) => v
    Err(e) =>
      match e {
        Sig(sig_e) => return Err(Sig(sig_e))
        Logic(logic_e) => return Err(Logic(logic_e))
        _ => return Err(Bridge(e))
      }
  }
  let steps : Array[TacticStep] = []
  for s in syn.steps {
    steps.push(step_from_syn(s))
  }
  let ps0 = ps_init(goal)
  let ps1 = match ps_apply_script(st1, prelude, ps0, steps) {
    Ok(v) => v
    Err(e) => return Err(Tactic(e))
  }
  match ps_qed(ps1) {
    Ok(th) => Ok((st1, th))
    Err(e) => Err(Tactic(e))
  }
}

///|
pub fn prover_phase0_ready() -> Bool {
  true
}
