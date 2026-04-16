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
pub fn local_hyp_name(hyp : LocalHyp) -> String {
  hyp.name
}

///|
pub fn local_hyp_term(hyp : LocalHyp) -> Term {
  hyp.term
}

///|
pub enum PendingRefine {
  ImpBackwardTerm(Term)
  ImpBackwardTheorem(Thm)
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
pub fn pending_goal_hyps(goal : PendingGoal) -> Array[Term] {
  goal.hyps.copy()
}

///|
pub fn pending_goal_concl(goal : PendingGoal) -> Term {
  goal.concl
}

///|
pub fn pending_goal_locals(goal : PendingGoal) -> Array[LocalHyp] {
  goal.locals.copy()
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
pub fn ps_current_pending_goal(ps : ProofState) -> PendingGoal? {
  if ps.pending.length() == 0 {
    None
  } else {
    Some(ps.pending[0])
  }
}

///|
pub fn ps_current_local_hyps(ps : ProofState) -> Array[LocalHyp] {
  match ps_current_pending_goal(ps) {
    Some(goal) => goal.locals.copy()
    None => []
  }
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
fn local_ref_bindings(locals : Array[LocalHyp]) -> Array[(String, Term)] {
  let out : Array[(String, Term)] = []
  for item in locals {
    out.push((item.name, item.term))
  }
  out
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
fn fact_pool(g : PendingGoal) -> Array[Term] {
  let out : Array[Term] = []
  for h in g.hyps {
    out.push(h)
  }
  for item in g.locals {
    out.push(item.term)
  }
  out
}

///|
fn exact_from_local_witness(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  g : PendingGoal,
  rest : Array[PendingGoal],
  _name : String,
) -> Result[ProofState, TacticExecError] {
  let base = match logic_prop_close_hypothesis(state, g.hyps, g.concl) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  finish_goal_evidence(state, prelude, ps, g, rest, base)
}

///|
fn exact_from_theorem(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  g : PendingGoal,
  rest : Array[PendingGoal],
  theorem : Thm,
) -> Result[ProofState, TacticExecError] {
  let checked = match
    logic_prop_ensure_sequent(state, g.hyps, g.concl, theorem) {
    Ok(v) => v
    Err(_) =>
      return Err(
        GoalShapeMismatch("exact theorem does not directly close current goal"),
      )
  }
  finish_goal_evidence(state, prelude, ps, g, rest, checked)
}

///|
fn exact_from_witness(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  g : PendingGoal,
  rest : Array[PendingGoal],
  witness : PropExactWitness,
) -> Result[ProofState, TacticExecError] {
  match witness {
    ExactLocalAlias(name) =>
      exact_from_local_witness(state, prelude, ps, g, rest, name)
    ExactDirectTheorem(_, theorem) =>
      exact_from_theorem(state, prelude, ps, g, rest, theorem)
    ExactContextTheorem(_, theorem, _) =>
      exact_from_theorem(state, prelude, ps, g, rest, theorem)
  }
}

///|
fn named_exact_mismatch() -> TacticExecError {
  GoalShapeMismatch("exact witness does not directly close current goal")
}

///|
fn named_apply_mismatch() -> TacticExecError {
  ApplyMismatch("named theorem does not apply to current goal")
}

///|
fn validate_root_theorem(
  state : KernelState,
  th : Thm,
  root : Goal,
  _prelude : PropPrelude,
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
  if !(term_logical_eq(cc_nf, rc_nf) || term_alpha_eq(cc_nf, rc_nf)) {
    return Err(
      ProofSynthesisUnavailable(
        "final theorem conclusion does not match root goal",
      ),
    )
  }
  Ok(())
}

///|
fn finalize_completed_theorem(
  state : KernelState,
  prelude : PropPrelude,
  root : Goal,
  rest : Array[PendingGoal],
  th : Thm,
) -> Result[ProofState, TacticExecError] {
  if rest.length() == 0 {
    match validate_root_theorem(state, th, root, prelude) {
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
fn replay_goal_refines(
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
      ImpBackwardTerm(imp_t) =>
        match
          logic_prop_replay_imp_elim_backward(state, prelude, g.hyps, imp_t, t) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
      ImpBackwardTheorem(imp_th) =>
        match
          logic_prop_replay_imp_elim_backward_thm(
            state,
            prelude,
            g.hyps,
            imp_th,
            t,
          ) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
    }
  }
  Ok(t)
}

///|
fn wrap_and_discharge_goal(
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
fn merge_split_goal_evidence(
  state : KernelState,
  prelude : PropPrelude,
  left_th : Thm,
  right_th : Thm,
  and_term : Term,
) -> Result[Thm, TacticExecError] {
  match
    logic_prop_merge_conjunction(state, prelude, left_th, right_th, and_term) {
    Ok(v) => Ok(v)
    Err(e) => Err(Logic(e))
  }
}

///|
fn store_split_left_partner(
  root : Goal,
  rest : Array[PendingGoal],
  and_term : Term,
  replayed : Thm,
) -> Result[ProofState, TacticExecError] {
  match split_pending_tail(rest) {
    Some((hd, tl)) =>
      match hd.split_role {
        SplitRight(c2, None) =>
          if term_alpha_eq(and_term, c2) {
            let hd2 = PendingGoal::{
              hyps: hd.hyps,
              concl: hd.concl,
              locals: hd.locals,
              imp_prefix: hd.imp_prefix,
              refine_chain: hd.refine_chain,
              split_role: SplitRight(c2, Some(replayed)),
              or_ctx: hd.or_ctx,
            }
            Ok(ProofState::{
              root_goal: root,
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
}

///|
priv enum GoalEvidenceAdvance {
  Waiting(ProofState)
  Completed(Thm)
}

///|
fn advance_goal_evidence(
  state : KernelState,
  prelude : PropPrelude,
  root : Goal,
  g : PendingGoal,
  rest : Array[PendingGoal],
  replayed : Thm,
) -> Result[GoalEvidenceAdvance, TacticExecError] {
  match g.split_role {
    SplitNone =>
      match wrap_and_discharge_goal(state, prelude, g, replayed) {
        Ok(v) => Ok(Completed(v))
        Err(e) => Err(e)
      }
    SplitLeft(and_term) =>
      match store_split_left_partner(root, rest, and_term, replayed) {
        Ok(v) => Ok(Waiting(v))
        Err(e) => Err(e)
      }
    SplitRight(and_term, Some(th_l)) => {
      let merged = match
        merge_split_goal_evidence(state, prelude, th_l, replayed, and_term) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      match wrap_and_discharge_goal(state, prelude, g, merged) {
        Ok(v) => Ok(Completed(v))
        Err(e) => Err(e)
      }
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
fn finish_goal_evidence(
  state : KernelState,
  prelude : PropPrelude,
  ps : ProofState,
  g : PendingGoal,
  rest : Array[PendingGoal],
  base_th : Thm,
) -> Result[ProofState, TacticExecError] {
  let replayed = match replay_goal_refines(state, prelude, g, base_th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match advance_goal_evidence(state, prelude, ps.root_goal, g, rest, replayed) {
    Ok(Waiting(next_ps)) => Ok(next_ps)
    Ok(Completed(th)) =>
      finalize_completed_theorem(state, prelude, ps.root_goal, rest, th)
    Err(e) => Err(e)
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
      match
        logic_prop_resolve_exact_witness(
          state,
          prelude,
          local_ref_bindings(g.locals),
          g.hyps,
          g.concl,
          name,
        ) {
        Some(PropExactWitnessResolution::ExactWitnessApplicable(witness)) =>
          exact_from_witness(state, prelude, ps, g, rest, witness)
        Some(PropExactWitnessResolution::ExactWitnessKnownButUnavailable) =>
          Err(named_exact_mismatch())
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
                rc.push(ImpBackwardTerm(local_term))
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
          if name == "imp_elim" {
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
                rc.push(ImpBackwardTerm(imp_t))
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
            match
              logic_prop_resolve_apply_theorem(
                state,
                prelude,
                fact_pool(g),
                g.concl,
                name,
              ) {
              Some(PropApplyTheoremResolution::Applicable(th, antecedent)) => {
                let rc = g.refine_chain.copy()
                rc.push(ImpBackwardTheorem(th))
                let (oh, ol, oip, _orc) = copy_goal_shape(g)
                keep_one(PendingGoal::{
                  hyps: oh,
                  concl: antecedent,
                  locals: ol,
                  imp_prefix: oip,
                  refine_chain: rc,
                  split_role: g.split_role,
                  or_ctx: g.or_ctx,
                })
              }
              Some(PropApplyTheoremResolution::KnownButUnavailable) =>
                Err(named_apply_mismatch())
              None => Err(UnknownName(name))
            }
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
