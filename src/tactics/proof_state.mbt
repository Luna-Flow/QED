///|
pub enum TacticStep {
  Intro(String)
  Exact(String)
  Apply(String)
  Assumption
  Split
  Left
  Right
}

///|
pub fn step_intro(name : String) -> TacticStep {
  Intro(name)
}

///|
pub fn step_exact(name : String) -> TacticStep {
  Exact(name)
}

///|
pub fn step_apply(name : String) -> TacticStep {
  Apply(name)
}

///|
pub fn step_assumption() -> TacticStep {
  Assumption
}

///|
pub fn step_split() -> TacticStep {
  Split
}

///|
pub fn step_left() -> TacticStep {
  Left
}

///|
pub fn step_right() -> TacticStep {
  Right
}

///|
pub enum TacticExecError {
  UnknownName(String)
  GoalShapeMismatch(String)
  ApplyMismatch(String)
  NoGoals
  UnsolvedGoals
  ProofSynthesisUnavailable(String)
  Logic(LogicError)
}

///|
pub struct LocalHyp {
  name : String
  term : Term
}

///|
pub struct PendingGoal {
  hyps : Array[Term]
  concl : Term
  locals : Array[LocalHyp]
}

///|
pub struct ProofState {
  root_goal : Goal
  pending : Array[PendingGoal]
  final_thm : Thm?
}

///|
fn pending_from_goal(goal : Goal) -> PendingGoal {
  PendingGoal::{ hyps: goal_hyps(goal), concl: goal_concl(goal), locals: [] }
}

///|
pub fn ps_init(goal : Goal) -> ProofState {
  ProofState::{
    root_goal: goal,
    pending: [pending_from_goal(goal)],
    final_thm: None,
  }
}

///|
pub fn ps_goal_count(ps : ProofState) -> Int {
  ps.pending.length()
}

///|
pub fn ps_current_goal(ps : ProofState) -> Goal? {
  if ps.pending.length() == 0 {
    None
  } else {
    let g = ps.pending[0]
    Some(mk_goal(g.hyps, g.concl))
  }
}

///|
fn split_pending_tail(
  pending : Array[PendingGoal],
) -> (PendingGoal, Array[PendingGoal])? {
  if pending.length() == 0 {
    None
  } else {
    let head = pending[0]
    let tail : Array[PendingGoal] = []
    let mut i = 1
    while i < pending.length() {
      tail.push(pending[i])
      i = i + 1
    }
    Some((head, tail))
  }
}

///|
fn concat_pending(
  prefix : Array[PendingGoal],
  suffix : Array[PendingGoal],
) -> Array[PendingGoal] {
  let out : Array[PendingGoal] = []
  for g in prefix {
    out.push(g)
  }
  for g in suffix {
    out.push(g)
  }
  out
}

///|
fn find_local(locals : Array[LocalHyp], name : String) -> Term? {
  let mut i = locals.length()
  while i > 0 {
    i = i - 1
    let item = locals[i]
    if item.name == name {
      return Some(item.term)
    }
  }
  None
}

///|
fn hyps_have_alpha(hyps : Array[Term], term : Term) -> Bool {
  hyps.any(fn(h) { term_alpha_eq(h, term) })
}

///|
fn find_imp_antecedent(
  prelude : PropPrelude,
  pool : Array[Term],
  concl : Term,
) -> Term? {
  for t in pool {
    match prop_dest_imp(prelude, t) {
      Some((a, b)) if term_alpha_eq(b, concl) => return Some(a)
      _ => ()
    }
  }
  None
}

///|
fn find_and_owner(
  prelude : PropPrelude,
  pool : Array[Term],
  want_left : Bool,
  concl : Term,
) -> Term? {
  for t in pool {
    match prop_dest_and(prelude, t) {
      Some((l, r)) =>
        if (want_left && term_alpha_eq(l, concl)) ||
          (!want_left && term_alpha_eq(r, concl)) {
          return Some(t)
        }
      _ => ()
    }
  }
  None
}

///|
pub fn ps_apply(
  _state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  step : TacticStep,
) -> Result[ProofState, TacticExecError] {
  let (g, rest) = match split_pending_tail(ps.pending) {
    Some(v) => v
    None => return Err(NoGoals)
  }

  let solved = fn() {
    Ok(ProofState::{ root_goal: ps.root_goal, pending: rest, final_thm: None })
  }

  let keep_one = fn(next : PendingGoal) {
    Ok(ProofState::{
      root_goal: ps.root_goal,
      pending: concat_pending([next], rest),
      final_thm: None,
    })
  }

  let keep_two = fn(next1 : PendingGoal, next2 : PendingGoal) {
    Ok(ProofState::{
      root_goal: ps.root_goal,
      pending: concat_pending([next1, next2], rest),
      final_thm: None,
    })
  }

  match step {
    Assumption =>
      if hyps_have_alpha(g.hyps, g.concl) {
        solved()
      } else {
        Err(GoalShapeMismatch("assumption cannot close current goal"))
      }
    Exact(name) =>
      match find_local(g.locals, name) {
        Some(t) =>
          if term_alpha_eq(t, g.concl) {
            solved()
          } else {
            Err(
              GoalShapeMismatch("exact name does not match current conclusion"),
            )
          }
        None => Err(UnknownName(name))
      }
    Intro(name) =>
      match prop_dest_imp(prelude, g.concl) {
        Some((a, b)) => {
          let hyps = g.hyps.copy()
          hyps.push(a)
          let locals = g.locals.copy()
          locals.push(LocalHyp::{ name, term: a })
          keep_one(PendingGoal::{ hyps, concl: b, locals })
        }
        None => Err(GoalShapeMismatch("intro requires an implication goal"))
      }
    Split =>
      match prop_dest_and(prelude, g.concl) {
        Some((a, b)) => {
          let g1 = PendingGoal::{
            hyps: g.hyps.copy(),
            concl: a,
            locals: g.locals.copy(),
          }
          let g2 = PendingGoal::{
            hyps: g.hyps.copy(),
            concl: b,
            locals: g.locals.copy(),
          }
          keep_two(g1, g2)
        }
        None => Err(GoalShapeMismatch("split requires a conjunction goal"))
      }
    Left =>
      match prop_dest_or(prelude, g.concl) {
        Some((a, _)) =>
          keep_one(PendingGoal::{
            hyps: g.hyps.copy(),
            concl: a,
            locals: g.locals.copy(),
          })
        None => Err(GoalShapeMismatch("left requires a disjunction goal"))
      }
    Right =>
      match prop_dest_or(prelude, g.concl) {
        Some((_, b)) =>
          keep_one(PendingGoal::{
            hyps: g.hyps.copy(),
            concl: b,
            locals: g.locals.copy(),
          })
        None => Err(GoalShapeMismatch("right requires a disjunction goal"))
      }
    Apply(name) =>
      match find_local(g.locals, name) {
        Some(local_term) =>
          match prop_dest_imp(prelude, local_term) {
            Some((a, b)) =>
              if term_alpha_eq(b, g.concl) {
                keep_one(PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: a,
                  locals: g.locals.copy(),
                })
              } else {
                Err(
                  ApplyMismatch(
                    "local implication does not target current goal",
                  ),
                )
              }
            None => Err(ApplyMismatch("local name is not an implication"))
          }
        None =>
          if !prop_prelude_has_rule(prelude, name) {
            Err(UnknownName(name))
          } else if name == "and_elim_l" || name == "and_elim_r" {
            let pool : Array[Term] = []
            for h in g.hyps {
              pool.push(h)
            }
            for l in g.locals {
              pool.push(l.term)
            }
            let want_left = name == "and_elim_l"
            match find_and_owner(prelude, pool, want_left, g.concl) {
              Some(owner) =>
                keep_one(PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: owner,
                  locals: g.locals.copy(),
                })
              None =>
                Err(
                  ApplyMismatch(
                    "cannot match conjunction eliminator to current goal",
                  ),
                )
            }
          } else if name == "imp_elim" {
            let pool : Array[Term] = []
            for h in g.hyps {
              pool.push(h)
            }
            for l in g.locals {
              pool.push(l.term)
            }
            match find_imp_antecedent(prelude, pool, g.concl) {
              Some(a) =>
                keep_one(PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: a,
                  locals: g.locals.copy(),
                })
              None =>
                Err(
                  ApplyMismatch(
                    "cannot match implication eliminator to current goal",
                  ),
                )
            }
          } else if name == "or_intro_l" {
            match prop_dest_or(prelude, g.concl) {
              Some((a, _)) =>
                keep_one(PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: a,
                  locals: g.locals.copy(),
                })
              None => Err(ApplyMismatch("or_intro_l requires disjunction goal"))
            }
          } else if name == "or_intro_r" {
            match prop_dest_or(prelude, g.concl) {
              Some((_, b)) =>
                keep_one(PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: b,
                  locals: g.locals.copy(),
                })
              None => Err(ApplyMismatch("or_intro_r requires disjunction goal"))
            }
          } else if name == "imp_intro" {
            match prop_dest_imp(prelude, g.concl) {
              Some((a, b)) => {
                let hyps = g.hyps.copy()
                hyps.push(a)
                let locals = g.locals.copy()
                locals.push(LocalHyp::{ name: "_h", term: a })
                keep_one(PendingGoal::{ hyps, concl: b, locals })
              }
              None => Err(ApplyMismatch("imp_intro requires implication goal"))
            }
          } else if name == "and_intro" {
            match prop_dest_and(prelude, g.concl) {
              Some((a, b)) => {
                let g1 = PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: a,
                  locals: g.locals.copy(),
                }
                let g2 = PendingGoal::{
                  hyps: g.hyps.copy(),
                  concl: b,
                  locals: g.locals.copy(),
                }
                keep_two(g1, g2)
              }
              None => Err(ApplyMismatch("and_intro requires conjunction goal"))
            }
          } else {
            Err(UnknownName(name))
          }
      }
  }
}

///|
pub fn ps_apply_script(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  steps : Array[TacticStep],
) -> Result[ProofState, TacticExecError] {
  let mut out = ps
  for st in steps {
    out = match ps_apply(state, prelude, out, st) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
  }
  Ok(out)
}

///|
pub fn ps_qed(ps : ProofState) -> Result[Thm, TacticExecError] {
  if ps.pending.length() != 0 {
    return Err(UnsolvedGoals)
  }
  match ps.final_thm {
    Some(th) => Ok(th)
    None =>
      Err(
        ProofSynthesisUnavailable(
          "proof state can solve goals operationally, but does not yet reconstruct a kernel theorem",
        ),
      )
  }
}

///|
pub fn tactics_proof_state_phase0_ready() -> Bool {
  true
}
