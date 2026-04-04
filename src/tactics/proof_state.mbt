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
pub enum PendingRefine {
  ImpBackward(Term)
  AndElimLeft(Term)
  AndElimRight(Term)
}

///|
pub enum SplitRole {
  SplitNone
  SplitLeft(Term)
  SplitRight(Term, Thm?)
}

///|
pub enum OrContext {
  OrNone
  OrPendingLeft(Term, Term)
  OrPendingRight(Term, Term)
}

///|
pub struct PendingGoal {
  hyps : Array[Term]
  concl : Term
  locals : Array[LocalHyp]
  imp_prefix : Array[Term]
  refine_chain : Array[PendingRefine]
  split_role : SplitRole
  or_ctx : OrContext
}

///|
pub struct ProofState {
  root_goal : Goal
  pending : Array[PendingGoal]
  final_thm : Thm?
}

///|
fn pending_from_goal(goal : Goal) -> PendingGoal {
  PendingGoal::{
    hyps: goal_hyps(goal),
    concl: goal_concl(goal),
    locals: [],
    imp_prefix: [],
    refine_chain: [],
    split_role: SplitNone,
    or_ctx: OrNone,
  }
}

///|
fn copy_goal_shape(
  g : PendingGoal,
) -> (Array[Term], Array[LocalHyp], Array[Term], Array[PendingRefine]) {
  (g.hyps.copy(), g.locals.copy(), g.imp_prefix.copy(), g.refine_chain.copy())
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
  hyps.any(fn(h) { term_logical_eq(h, term) || term_alpha_eq(h, term) })
}

///|
fn find_imp_antecedent_with_imp(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
  concl : Term,
) -> (Term, Term)? {
  for t in pool {
    match prop_dest_imp(state, prelude, t) {
      Some((a, b)) if term_logical_eq(b, concl) || term_alpha_eq(b, concl) =>
        return Some((a, t))
      _ => ()
    }
  }
  None
}

///|
fn find_and_owner(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
  want_left : Bool,
  concl : Term,
) -> Term? {
  for t in pool {
    match prop_dest_and(state, prelude, t) {
      Some((l, r)) =>
        if (want_left && (term_logical_eq(l, concl) || term_alpha_eq(l, concl))) ||
          (!want_left && (term_logical_eq(r, concl) || term_alpha_eq(r, concl))) {
          return Some(t)
        }
      _ => ()
    }
  }
  None
}

///|
fn root_concl_compat_or_tail(
  state : KernelState,
  prelude : PropPrelude,
  b1 : Term,
  b2 : Term,
) -> Bool {
  if term_logical_eq(b1, b2) || term_alpha_eq(b1, b2) {
    true
  } else {
    let n1 = match logic_beta_nf_bool_term_deep(state, b1) {
      Ok(v) => v
      Err(_) => b1
    }
    let n2 = match logic_beta_nf_bool_term_deep(state, b2) {
      Ok(v) => v
      Err(_) => b2
    }
    if term_logical_eq(n1, n2) || term_alpha_eq(n1, n2) {
      true
    } else {
      match
        (prop_dest_or(state, prelude, n1), prop_dest_or(state, prelude, n2)) {
        (Some((l1, r1)), Some((l2, r2))) =>
          root_concl_heads_match(state, l1, l2) &&
          root_concl_heads_match(state, r1, r2)
        _ => false
      }
    }
  }
}

///|
fn root_concl_heads_match(state : KernelState, t1 : Term, t2 : Term) -> Bool {
  if term_logical_eq(t1, t2) || term_alpha_eq(t1, t2) {
    true
  } else {
    let u1 = match logic_beta_nf_bool_term_deep(state, t1) {
      Ok(v) => v
      Err(_) => t1
    }
    let u2 = match logic_beta_nf_bool_term_deep(state, t2) {
      Ok(v) => v
      Err(_) => t2
    }
    term_logical_eq(u1, u2) || term_alpha_eq(u1, u2)
  }
}

///|
fn root_concl_compat(
  state : KernelState,
  prelude : PropPrelude,
  cc : Term,
  rc : Term,
) -> Bool {
  if term_logical_eq(cc, rc) || term_alpha_eq(cc, rc) {
    true
  } else {
    match
      (prop_dest_imp(state, prelude, cc), prop_dest_imp(state, prelude, rc)) {
      (Some((a1, b1)), Some((a2, b2))) =>
        root_concl_heads_match(state, a1, a2) &&
        root_concl_compat_or_tail(state, prelude, b1, b2)
      _ => false
    }
  }
}

///|
fn root_matches_thm(
  state : KernelState,
  th : Thm,
  root : Goal,
  prelude : PropPrelude,
) -> Result[Unit, TacticExecError] {
  let rhy = goal_hyps(root)
  let rc = goal_concl(root)
  let hs = match thm_hyps(th) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let th_norm = match logic_normalize_prop_beta(state, th) {
    Ok(v) => v
    Err(_) => th
  }
  let cc = match thm_concl(th_norm) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let rc_nf = match logic_beta_nf_bool_term_deep(state, rc) {
    Ok(v) => v
    Err(_) => rc
  }
  let cc_nf = match logic_beta_nf_bool_term_deep(state, cc) {
    Ok(v) => v
    Err(_) => cc
  }
  if rhy.length() != hs.length() {
    return Err(
      ProofSynthesisUnavailable(
        "final theorem hypotheses do not match root goal",
      ),
    )
  }
  let used : Array[Bool] = []
  let mut ui = 0
  while ui < hs.length() {
    used.push(false)
    ui = ui + 1
  }
  for h in rhy {
    let mut j = 0
    let mut matched = false
    while j < hs.length() {
      if !used[j] && term_logical_eq(h, hs[j]) {
        used[j] = true
        matched = true
        break
      }
      j = j + 1
    }
    if !matched {
      return Err(
        ProofSynthesisUnavailable(
          "final theorem hypotheses do not match root goal",
        ),
      )
    }
  }
  if !(root_concl_compat(state, prelude, cc_nf, rc_nf) ||
    term_logical_eq(cc_nf, rc_nf) ||
    term_alpha_eq(cc_nf, rc_nf)) {
    return Err(
      ProofSynthesisUnavailable(
        "final theorem conclusion does not match root goal",
      ),
    )
  }
  Ok(())
}

///|
fn propagate_finished(
  state : KernelState,
  prelude : PropPrelude,
  root : Goal,
  rest : Array[PendingGoal],
  th : Thm,
) -> Result[ProofState, TacticExecError] {
  if rest.length() == 0 {
    match root_matches_thm(state, th, root, prelude) {
      Ok(_) =>
        Ok(ProofState::{ root_goal: root, pending: [], final_thm: Some(th) })
      Err(e) => Err(e)
    }
  } else {
    Err(
      ProofSynthesisUnavailable(
        "internal proof synthesis: unexpected pending goals after subproof close",
      ),
    )
  }
}

///|
fn apply_base_and_refines(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  base_th : Thm,
) -> Result[Thm, TacticExecError] {
  let mut t = match logic_prop_ensure_sequent(state, g.hyps, g.concl, base_th) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let mut ri = g.refine_chain.length()
  while ri > 0 {
    ri = ri - 1
    t = match g.refine_chain[ri] {
      ImpBackward(imp_t) =>
        match
          logic_prop_replay_imp_elim_backward(state, prelude, g.hyps, imp_t, t) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
      AndElimLeft(exp) =>
        match logic_prop_replay_and_elim_l(state, prelude, exp, t) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
      AndElimRight(exp) =>
        match logic_prop_replay_and_elim_r(state, prelude, exp, t) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
    }
  }
  Ok(t)
}

///|
fn discharge_or_wrap_goal(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  t : Thm,
) -> Result[Thm, TacticExecError] {
  let mut u = match g.or_ctx {
    OrNone => t
    OrPendingLeft(fo, rb) =>
      match logic_prop_or_wrap_left(state, prelude, fo, rb, t) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
    OrPendingRight(fo, lb) =>
      match logic_prop_or_wrap_right(state, prelude, fo, lb, t) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
  }
  u = match logic_prop_discharge_imp_prefix(state, prelude, g.imp_prefix, u) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  Ok(u)
}

///|
fn finish_goal_evidence(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  g : PendingGoal,
  rest : Array[PendingGoal],
  base_th : Thm,
) -> Result[ProofState, TacticExecError] {
  let t = match apply_base_and_refines(state, prelude, g, base_th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match g.split_role {
    SplitNone => {
      let t2 = match discharge_or_wrap_goal(state, prelude, g, t) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      propagate_finished(state, prelude, ps.root_goal, rest, t2)
    }
    SplitLeft(and_c) =>
      match split_pending_tail(rest) {
        Some((hd, tl)) =>
          match hd.split_role {
            SplitRight(c2, None) =>
              if term_alpha_eq(and_c, c2) {
                let hd2 = PendingGoal::{
                  hyps: hd.hyps,
                  concl: hd.concl,
                  locals: hd.locals,
                  imp_prefix: hd.imp_prefix,
                  refine_chain: hd.refine_chain,
                  split_role: SplitRight(c2, Some(t)),
                  or_ctx: hd.or_ctx,
                }
                Ok(ProofState::{
                  root_goal: ps.root_goal,
                  pending: concat_pending([hd2], tl),
                  final_thm: None,
                })
              } else {
                Err(GoalShapeMismatch("split conjunction mismatch"))
              }
            _ => Err(GoalShapeMismatch("expected split right partner"))
          }
        None => Err(GoalShapeMismatch("missing split partner goal"))
      }
    SplitRight(and_c, Some(th_l)) => {
      let th_m = match
        logic_prop_merge_conjunction(state, prelude, th_l, t, and_c) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
      let t2 = match discharge_or_wrap_goal(state, prelude, g, th_m) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      propagate_finished(state, prelude, ps.root_goal, rest, t2)
    }
    SplitRight(_, None) =>
      Err(
        ProofSynthesisUnavailable(
          "internal: closed split right goal without partner evidence",
        ),
      )
  }
}

///|
pub fn ps_apply(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  step : TacticStep,
) -> Result[ProofState, TacticExecError] {
  let (g, rest) = match split_pending_tail(ps.pending) {
    Some(v) => v
    None => return Err(NoGoals)
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
        let base = match logic_prop_close_hypothesis(state, g.hyps, g.concl) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
        finish_goal_evidence(state, prelude, ps, g, rest, base)
      } else {
        Err(GoalShapeMismatch("assumption cannot close current goal"))
      }
    Exact(name) =>
      match find_local(g.locals, name) {
        Some(t) => {
          let hyp_bridge = g.hyps.any(fn(h) {
            (term_logical_eq(h, g.concl) || term_alpha_eq(h, g.concl)) &&
            (term_logical_eq(t, h) || term_alpha_eq(t, h))
          })
          let concl_ok = term_logical_eq(t, g.concl) ||
            term_alpha_eq(t, g.concl) ||
            hyp_bridge
          if concl_ok {
            let base = match
              logic_prop_close_hypothesis(state, g.hyps, g.concl) {
              Ok(v) => v
              Err(e) => return Err(Logic(e))
            }
            finish_goal_evidence(state, prelude, ps, g, rest, base)
          } else {
            Err(
              GoalShapeMismatch("exact name does not match current conclusion"),
            )
          }
        }
        None => Err(UnknownName(name))
      }
    Intro(name) =>
      match prop_dest_imp(state, prelude, g.concl) {
        Some((a, b)) => {
          let hyps = g.hyps.copy()
          hyps.push(a)
          let locals = g.locals.copy()
          locals.push(LocalHyp::{ name, term: a })
          let ip = g.imp_prefix.copy()
          ip.push(a)
          keep_one(PendingGoal::{
            hyps,
            concl: b,
            locals,
            imp_prefix: ip,
            refine_chain: [],
            split_role: g.split_role,
            or_ctx: g.or_ctx,
          })
        }
        None => Err(GoalShapeMismatch("intro requires an implication goal"))
      }
    Split =>
      match prop_dest_and(state, prelude, g.concl) {
        Some((a, b)) => {
          let and_full = g.concl
          let (oh, ol, oip, orc) = copy_goal_shape(g)
          let g1 = PendingGoal::{
            hyps: oh.copy(),
            concl: a,
            locals: ol.copy(),
            imp_prefix: oip.copy(),
            refine_chain: orc.copy(),
            split_role: SplitLeft(and_full),
            or_ctx: g.or_ctx,
          }
          let g2 = PendingGoal::{
            hyps: oh,
            concl: b,
            locals: ol,
            imp_prefix: oip,
            refine_chain: orc,
            split_role: SplitRight(and_full, None),
            or_ctx: g.or_ctx,
          }
          keep_two(g1, g2)
        }
        None => Err(GoalShapeMismatch("split requires a conjunction goal"))
      }
    Left =>
      match prop_dest_or(state, prelude, g.concl) {
        Some((a, br)) => {
          let (oh, ol, oip, orc) = copy_goal_shape(g)
          keep_one(PendingGoal::{
            hyps: oh,
            concl: a,
            locals: ol,
            imp_prefix: oip,
            refine_chain: orc,
            split_role: g.split_role,
            or_ctx: OrPendingLeft(g.concl, br),
          })
        }
        None => Err(GoalShapeMismatch("left requires a disjunction goal"))
      }
    Right =>
      match prop_dest_or(state, prelude, g.concl) {
        Some((al, b)) => {
          let (oh, ol, oip, orc) = copy_goal_shape(g)
          keep_one(PendingGoal::{
            hyps: oh,
            concl: b,
            locals: ol,
            imp_prefix: oip,
            refine_chain: orc,
            split_role: g.split_role,
            or_ctx: OrPendingRight(g.concl, al),
          })
        }
        None => Err(GoalShapeMismatch("right requires a disjunction goal"))
      }
    Apply(name) =>
      match find_local(g.locals, name) {
        Some(local_term) =>
          match prop_dest_imp(state, prelude, local_term) {
            Some((a, b)) =>
              if term_logical_eq(b, g.concl) || term_alpha_eq(b, g.concl) {
                let rc = g.refine_chain.copy()
                rc.push(ImpBackward(local_term))
                let (oh, ol, oip, _) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: a,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: rc,
                  split_role: g.split_role,
                  or_ctx: g.or_ctx,
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
            match find_and_owner(state, prelude, pool, want_left, g.concl) {
              Some(owner) => {
                let prev_concl = g.concl
                let rc = g.refine_chain.copy()
                rc.push(
                  if want_left {
                    AndElimLeft(prev_concl)
                  } else {
                    AndElimRight(prev_concl)
                  },
                )
                let (oh, ol, oip, _orc) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: owner,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: rc,
                  split_role: g.split_role,
                  or_ctx: g.or_ctx,
                })
              }
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
            match find_imp_antecedent_with_imp(state, prelude, pool, g.concl) {
              Some((a, imp_t)) => {
                let rc = g.refine_chain.copy()
                rc.push(ImpBackward(imp_t))
                let (oh, ol, oip, _orc) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: a,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: rc,
                  split_role: g.split_role,
                  or_ctx: g.or_ctx,
                })
              }
              None =>
                Err(
                  ApplyMismatch(
                    "cannot match implication eliminator to current goal",
                  ),
                )
            }
          } else if name == "or_intro_l" {
            match prop_dest_or(state, prelude, g.concl) {
              Some((a, br)) => {
                let (oh, ol, oip, orc) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: a,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: orc,
                  split_role: g.split_role,
                  or_ctx: OrPendingLeft(g.concl, br),
                })
              }
              None => Err(ApplyMismatch("or_intro_l requires disjunction goal"))
            }
          } else if name == "or_intro_r" {
            match prop_dest_or(state, prelude, g.concl) {
              Some((al, b)) => {
                let (oh, ol, oip, orc) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: b,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: orc,
                  split_role: g.split_role,
                  or_ctx: OrPendingRight(g.concl, al),
                })
              }
              None => Err(ApplyMismatch("or_intro_r requires disjunction goal"))
            }
          } else if name == "imp_intro" {
            match prop_dest_imp(state, prelude, g.concl) {
              Some((a, b)) => {
                let hyps = g.hyps.copy()
                hyps.push(a)
                let locals = g.locals.copy()
                locals.push(LocalHyp::{ name: "_h", term: a })
                let ip = g.imp_prefix.copy()
                ip.push(a)
                keep_one(PendingGoal::{
                  hyps,
                  concl: b,
                  locals,
                  imp_prefix: ip,
                  refine_chain: [],
                  split_role: g.split_role,
                  or_ctx: g.or_ctx,
                })
              }
              None => Err(ApplyMismatch("imp_intro requires implication goal"))
            }
          } else if name == "and_intro" {
            match prop_dest_and(state, prelude, g.concl) {
              Some((a, b)) => {
                let and_full = g.concl
                let (oh, ol, oip, orc) = copy_goal_shape(g)
                let g1 = PendingGoal::{
                  hyps: oh.copy(),
                  concl: a,
                  locals: ol.copy(),
                  imp_prefix: oip.copy(),
                  refine_chain: orc.copy(),
                  split_role: SplitLeft(and_full),
                  or_ctx: g.or_ctx,
                }
                let g2 = PendingGoal::{
                  hyps: oh,
                  concl: b,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: orc,
                  split_role: SplitRight(and_full, None),
                  or_ctx: g.or_ctx,
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
