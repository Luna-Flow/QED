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
pub fn tactic_goal_shape_mismatch(msg : String) -> TacticExecError {
  GoalShapeMismatch(msg)
}

///|
pub fn tactic_no_goals() -> TacticExecError {
  NoGoals
}

///|
struct LocalHyp {
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
struct ProofGoalView {
  goal : Goal
  locals : Array[LocalHyp]
  branch_path : Array[Int]
}

///|
pub fn proof_goal_view_goal(view : ProofGoalView) -> Goal {
  view.goal
}

///|
pub fn proof_goal_view_locals(view : ProofGoalView) -> Array[LocalHyp] {
  view.locals.copy()
}

///|
pub fn proof_goal_view_branch_path(view : ProofGoalView) -> Array[Int] {
  view.branch_path.copy()
}

///|
struct ProofStateSnapshot {
  root_goal : Goal
  pending_goal_count : Int
  current : ProofGoalView?
}

///|
pub fn proof_state_snapshot_root_goal(snapshot : ProofStateSnapshot) -> Goal {
  snapshot.root_goal
}

///|
pub fn proof_state_snapshot_pending_goal_count(
  snapshot : ProofStateSnapshot,
) -> Int {
  snapshot.pending_goal_count
}

///|
pub fn proof_state_snapshot_current(
  snapshot : ProofStateSnapshot,
) -> ProofGoalView? {
  snapshot.current
}

///|
pub enum PendingRefine {
  ImpBackwardTerm(Term)
  ImpBackwardTheorem(Thm)
  AbsBackwardTerm(Term, Term)
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
priv struct PendingGoal {
  hyps : Array[Term]
  concl : Term
  locals : Array[LocalHyp]
  branch_path : Array[Int]
  imp_prefix : Array[Term]
  refine_chain : Array[PendingRefine]
  split_role : SplitRole
  or_ctx : OrContext
}

///|
fn goal_view_of_pending(goal : PendingGoal) -> ProofGoalView {
  ProofGoalView::{
    goal: mk_goal(goal.hyps, goal.concl),
    locals: goal.locals,
    branch_path: goal.branch_path,
  }
}

///|
struct ProofState {
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
    branch_path: [],
    imp_prefix: [],
    refine_chain: [],
    split_role: SplitNone,
    or_ctx: OrNone,
  }
}

///|
fn copy_goal_shape(
  g : PendingGoal,
) -> (
  Array[Term],
  Array[LocalHyp],
  Array[Int],
  Array[Term],
  Array[PendingRefine],
) {
  (
    g.hyps.copy(),
    g.locals.copy(),
    g.branch_path.copy(),
    g.imp_prefix.copy(),
    g.refine_chain.copy(),
  )
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
fn ps_current_pending_goal(ps : ProofState) -> PendingGoal? {
  if ps.pending.length() == 0 {
    None
  } else {
    Some(ps.pending[0])
  }
}

///|
pub fn ps_root_goal(ps : ProofState) -> Goal {
  ps.root_goal
}

///|
pub fn ps_current_focus(ps : ProofState) -> ProofGoalView? {
  match ps_current_pending_goal(ps) {
    Some(goal) => Some(goal_view_of_pending(goal))
    None => None
  }
}

///|
pub fn ps_current_branch_path(ps : ProofState) -> Array[Int] {
  match ps_current_focus(ps) {
    Some(goal) => proof_goal_view_branch_path(goal)
    None => []
  }
}

///|
pub fn ps_pending_focus_at(ps : ProofState, idx : Int) -> ProofGoalView? {
  if idx < 0 || idx >= ps.pending.length() {
    None
  } else {
    Some(goal_view_of_pending(ps.pending[idx]))
  }
}

///|
pub fn ps_snapshot(ps : ProofState) -> ProofStateSnapshot {
  ProofStateSnapshot::{
    root_goal: ps.root_goal,
    pending_goal_count: ps.pending.length(),
    current: ps_current_focus(ps),
  }
}

///|
pub fn ps_current_local_hyps(ps : ProofState) -> Array[LocalHyp] {
  match ps_current_focus(ps) {
    Some(goal) => proof_goal_view_locals(goal)
    None => []
  }
}

///|
pub fn ps_current_goal(ps : ProofState) -> Goal? {
  match ps_current_focus(ps) {
    Some(goal) => Some(proof_goal_view_goal(goal))
    None => None
  }
}

///|
pub fn ps_pending_goal_at(ps : ProofState, idx : Int) -> Goal? {
  match ps_pending_focus_at(ps, idx) {
    Some(goal) => Some(proof_goal_view_goal(goal))
    None => None
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
fn child_branch_path(branch_path : Array[Int], branch_idx : Int) -> Array[Int] {
  let out = branch_path.copy()
  out.push(branch_idx)
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
  name : String,
) -> Result[ProofState, TacticExecError] {
  let local_term = match find_local(g.locals, name) {
    Some(v) => v
    None =>
      return Err(
        GoalShapeMismatch(
          "exact local witness is no longer an active hypothesis alias",
        ),
      )
  }
  if !(term_logical_eq(local_term, g.concl) ||
    term_alpha_eq(local_term, g.concl)) {
    return Err(
      GoalShapeMismatch(
        "exact local witness does not directly close current goal",
      ),
    )
  }
  if !hyps_have_alpha(g.hyps, local_term) {
    return Err(
      GoalShapeMismatch(
        "exact local witness is no longer an active hypothesis alias",
      ),
    )
  }
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
  let th_norm = match logic_normalize_prop_beta(state, th) {
    Ok(v) => v
    Err(_) => th
  }
  let rhy = goal_hyps(root)
  let rc = goal_concl(root)
  let hs = match thm_hyps(th_norm) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let cc = match thm_concl(th_norm) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let nf_term = fn(term : Term) {
    match logic_beta_nf_bool_term_deep(state, term) {
      Ok(v) => v
      Err(_) => term
    }
  }
  let rc_nf = nf_term(rc)
  let cc_nf = nf_term(cc)
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
    let h_nf = nf_term(h)
    let mut j = 0
    let mut matched = false
    while j < hs.length() {
      let hs_nf = nf_term(hs[j])
      if !used[j] &&
        (term_logical_eq(h_nf, hs_nf) || term_alpha_eq(h_nf, hs_nf)) {
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
    t = match
      replay_goal_refines_step(state, prelude, g, t, g.refine_chain[ri]) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
  }
  Ok(t)
}

///|
fn replay_goal_refines_step(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  t : Thm,
  refine : PendingRefine,
) -> Result[Thm, TacticExecError] {
  match refine {
    ImpBackwardTerm(imp_t) => {
      let replayed = logic_prop_replay_imp_elim_backward(
        state,
        prelude,
        g.hyps,
        imp_t,
        t,
      )
      match replayed {
        Ok(v) => Ok(v)
        Err(e) => Err(Logic(e))
      }
    }
    ImpBackwardTheorem(imp_th) => {
      let replayed = logic_prop_replay_imp_elim_backward_thm(
        state,
        prelude,
        g.hyps,
        imp_th,
        t,
      )
      match replayed {
        Ok(v) => Ok(v)
        Err(e) => Err(Logic(e))
      }
    }
    AbsBackwardTerm(_, _) => Ok(t)
  }
}

///|
fn replay_goal_abs_refines(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  base_th : Thm,
) -> Result[Thm, TacticExecError] {
  let mut t = base_th
  let mut ri = g.refine_chain.length()
  while ri > 0 {
    ri = ri - 1
    let next = replay_goal_abs_refines_step(
      state,
      prelude,
      g.refine_chain[ri],
      t,
    )
    t = match next {
      Ok(v) => v
      Err(e) => return Err(e)
    }
  }
  Ok(t)
}

///|
fn replay_goal_abs_refines_step(
  state : KernelState,
  prelude : PropPrelude,
  refine : PendingRefine,
  t : Thm,
) -> Result[Thm, TacticExecError] {
  match refine {
    AbsBackwardTerm(user_binder, hidden_binder) => {
      let truth = match @logic.logic_prop_truth_const_thm(state, prelude) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
      let lifted = match @logic.logic_deduct_antisym(state, t, truth) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
      let lifted_attempt = logic_inst(
        state,
        [(user_binder, hidden_binder)],
        lifted,
      )
      match lifted_attempt {
        Ok(instantiated) =>
          match @logic.logic_abs_rule(state, hidden_binder, instantiated) {
            Ok(v) => Ok(v)
            Err(e) => Err(Logic(e))
          }
        Err(_) =>
          match @logic.logic_abs_rule(state, user_binder, lifted) {
            Ok(v) => Ok(v)
            Err(e) => Err(Logic(e))
          }
      }
    }
    _ => Ok(t)
  }
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
  replay_goal_abs_refines(state, prelude, g, u)
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
              branch_path: hd.branch_path,
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
priv enum ApplyAcceptance {
  KeepOne(PendingGoal)
  KeepTwo(PendingGoal, PendingGoal)
}

///|
fn apply_refine_goal(
  g : PendingGoal,
  antecedent : Term,
  refine : PendingRefine,
) -> ApplyAcceptance {
  let rc = g.refine_chain.copy()
  rc.push(refine)
  let (oh, ol, obp, oip, _orc) = copy_goal_shape(g)
  KeepOne(PendingGoal::{
    hyps: oh,
    concl: antecedent,
    locals: ol,
    branch_path: obp,
    imp_prefix: oip,
    refine_chain: rc,
    split_role: g.split_role,
    or_ctx: g.or_ctx,
  })
}

///|
fn pending_goal_after_intro(
  g : PendingGoal,
  name : String,
  intro_term : Term,
  concl : Term,
  refine : PendingRefine?,
  push_hyp : Bool,
  push_imp_prefix : Bool,
) -> PendingGoal {
  let (hyps, locals, branch_path, ip, refines) = copy_goal_shape(g)
  if push_hyp {
    hyps.push(intro_term)
  }
  let locals = locals
  locals.push(LocalHyp::{ name, term: intro_term })
  if push_imp_prefix {
    ip.push(intro_term)
  }
  let refines = refines
  match refine {
    Some(r) => refines.push(r)
    None => ()
  }
  PendingGoal::{
    hyps,
    concl,
    locals,
    branch_path,
    imp_prefix: ip,
    refine_chain: refines,
    split_role: g.split_role,
    or_ctx: g.or_ctx,
  }
}

///|
fn apply_accept_local_term(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  local_term : Term,
) -> Result[ApplyAcceptance, TacticExecError] {
  match prop_dest_imp(state, prelude, local_term) {
    Some((a, b)) =>
      if term_logical_eq(b, g.concl) || term_alpha_eq(b, g.concl) {
        Ok(apply_refine_goal(g, a, ImpBackwardTerm(local_term)))
      } else {
        Err(ApplyMismatch("local implication does not target current goal"))
      }
    None => Err(ApplyMismatch("local name is not an implication"))
  }
}

///|
fn apply_accept_local_name(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  name : String,
) -> Result[ApplyAcceptance?, TacticExecError] {
  match find_local(g.locals, name) {
    Some(local_term) =>
      match apply_accept_local_term(state, prelude, g, local_term) {
        Ok(v) => Ok(Some(v))
        Err(e) => Err(e)
      }
    None => Ok(None)
  }
}

///|
fn apply_accept_imp_elim(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
) -> Result[ApplyAcceptance, TacticExecError] {
  match find_imp_antecedent_with_imp(state, prelude, fact_pool(g), g.concl) {
    Some((a, imp_t)) => Ok(apply_refine_goal(g, a, ImpBackwardTerm(imp_t)))
    None =>
      Err(ApplyMismatch("cannot match implication eliminator to current goal"))
  }
}

///|
fn apply_accept_imp_intro(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
) -> Result[ApplyAcceptance, TacticExecError] {
  match prop_dest_imp(state, prelude, g.concl) {
    Some((a, b)) =>
      Ok(KeepOne(pending_goal_after_intro(g, "_h", a, b, None, true, true)))
    None => Err(ApplyMismatch("imp_intro requires implication goal"))
  }
}

///|

///|
fn apply_accept_and_intro(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
) -> Result[ApplyAcceptance, TacticExecError] {
  match prop_dest_and(state, prelude, g.concl) {
    Some((a, b)) => {
      let and_full = g.concl
      let (oh, ol, obp, oip, orc) = copy_goal_shape(g)
      let g1 = PendingGoal::{
        hyps: oh.copy(),
        concl: a,
        locals: ol.copy(),
        branch_path: child_branch_path(obp, 1),
        imp_prefix: oip.copy(),
        refine_chain: orc.copy(),
        split_role: SplitLeft(and_full),
        or_ctx: g.or_ctx,
      }
      let g2 = PendingGoal::{
        hyps: oh,
        concl: b,
        locals: ol,
        branch_path: child_branch_path(obp, 2),
        imp_prefix: oip,
        refine_chain: orc,
        split_role: SplitRight(and_full, None),
        or_ctx: g.or_ctx,
      }
      Ok(KeepTwo(g1, g2))
    }
    None => Err(ApplyMismatch("and_intro requires conjunction goal"))
  }
}

///|
fn term_uses_var_name(term : Term, name : String) -> Bool {
  let vars = @kernel.free_vars(term)
  let mut i = 0
  while i < vars.length() {
    let (var_name, _) = vars[i]
    if var_name == name {
      return true
    }
    i = i + 1
  }
  false
}

///|
fn replay_binder_name_in_use(
  g : PendingGoal,
  binder : Term,
  body : Term,
  rhs_body : Term,
  name : String,
) -> Bool {
  if term_uses_var_name(binder, name) ||
    term_uses_var_name(body, name) ||
    term_uses_var_name(rhs_body, name) {
    return true
  }
  for hyp in g.hyps {
    if term_uses_var_name(hyp, name) {
      return true
    }
  }
  for item in g.locals {
    if item.name == name || term_uses_var_name(item.term, name) {
      return true
    }
  }
  false
}

///|
fn fresh_quantified_replay_binder(
  g : PendingGoal,
  binder : Term,
  body : Term,
  rhs_body : Term,
) -> Result[Term, TacticExecError] {
  let ty = match type_of(binder) {
    Some(v) => v
    None =>
      return Err(
        ProofSynthesisUnavailable("quantified intro needs binder type"),
      )
  }
  let mut idx = g.refine_chain.length()
  while true {
    let name = "_b" + idx.to_string()
    if !replay_binder_name_in_use(g, binder, body, rhs_body, name) {
      return Ok(mk_var(name, ty))
    }
    idx = idx + 1
  }
  Err(
    ProofSynthesisUnavailable(
      "internal: fresh quantified replay binder generation did not terminate",
    ),
  )
}

///|
fn quantified_intro_truth_term(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Term, TacticExecError] {
  let truth_term = match ks_definition_theorem(state, prelude.truth_name) {
    Ok(th) =>
      match thm_concl(th) {
        Ok(concl) =>
          match @kernel.dest_eq(concl) {
            Ok((lhs, _)) => lhs
            Err(_) =>
              return Err(
                ProofSynthesisUnavailable(
                  "quantified intro needs truth constant",
                ),
              )
          }
        Err(_) =>
          return Err(
            ProofSynthesisUnavailable("quantified intro needs truth constant"),
          )
      }
    Err(_) =>
      return Err(
        ProofSynthesisUnavailable("quantified intro needs truth constant"),
      )
  }
  Ok(truth_term)
}

///|
fn intro_quantified_goal(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  name : String,
) -> Result[PendingGoal, TacticExecError] {
  match @kernel.dest_eq(g.concl) {
    Ok((lhs, rhs)) =>
      match (@kernel.dest_abs(lhs), @kernel.dest_abs(rhs)) {
        (Some((binder, body)), Some((_, rhs_body))) => {
          let truth_term = match quantified_intro_truth_term(state, prelude) {
            Ok(v) => v
            Err(e) => return Err(e)
          }
          if term_logical_eq(rhs_body, truth_term) ||
            term_alpha_eq(rhs_body, truth_term) {
            let replay_binder = match
              fresh_quantified_replay_binder(g, binder, body, rhs_body) {
              Ok(v) => v
              Err(e) => return Err(e)
            }
            Ok(
              pending_goal_after_intro(
                g,
                name,
                binder,
                body,
                Some(AbsBackwardTerm(binder, replay_binder)),
                false,
                false,
              ),
            )
          } else {
            Err(
              GoalShapeMismatch(
                "intro requires an implication or quantified goal",
              ),
            )
          }
        }
        _ =>
          Err(
            GoalShapeMismatch(
              "intro requires an implication or quantified goal",
            ),
          )
      }
    Err(_) =>
      Err(GoalShapeMismatch("intro requires an implication or quantified goal"))
  }
}

///|
fn apply_accept_builtin(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  name : String,
) -> Result[ApplyAcceptance?, TacticExecError] {
  if name == "imp_elim" {
    match apply_accept_imp_elim(state, prelude, g) {
      Ok(v) => Ok(Some(v))
      Err(e) => Err(e)
    }
  } else if name == "imp_intro" {
    match apply_accept_imp_intro(state, prelude, g) {
      Ok(v) => Ok(Some(v))
      Err(e) => Err(e)
    }
  } else if name == "and_intro" {
    match apply_accept_and_intro(state, prelude, g) {
      Ok(v) => Ok(Some(v))
      Err(e) => Err(e)
    }
  } else {
    Ok(None)
  }
}

///|
fn apply_accept_theorem_name(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  name : String,
) -> Result[ApplyAcceptance, TacticExecError] {
  match
    logic_prop_resolve_apply_theorem(
      state,
      prelude,
      fact_pool(g),
      g.concl,
      name,
    ) {
    Some(PropApplyTheoremResolution::Applicable(th, antecedent)) =>
      Ok(apply_refine_goal(g, antecedent, ImpBackwardTheorem(th)))
    Some(PropApplyTheoremResolution::KnownButUnavailable) =>
      Err(named_apply_mismatch())
    None => Err(UnknownName(name))
  }
}

///|
fn apply_accept_name(
  state : KernelState,
  prelude : PropPrelude,
  g : PendingGoal,
  name : String,
) -> Result[ApplyAcceptance, TacticExecError] {
  match apply_accept_local_name(state, prelude, g, name) {
    Ok(Some(v)) => Ok(v)
    Ok(None) =>
      match apply_accept_builtin(state, prelude, g, name) {
        Ok(Some(v)) => Ok(v)
        Ok(None) => apply_accept_theorem_name(state, prelude, g, name)
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
fn apply_acceptance_state(
  root : Goal,
  rest : Array[PendingGoal],
  accepted : ApplyAcceptance,
) -> ProofState {
  match accepted {
    KeepOne(next) =>
      ProofState::{
        root_goal: root,
        pending: concat_pending([next], rest),
        final_thm: None,
      }
    KeepTwo(next1, next2) =>
      ProofState::{
        root_goal: root,
        pending: concat_pending([next1, next2], rest),
        final_thm: None,
      }
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
        Some((a, b)) =>
          keep_one(pending_goal_after_intro(g, name, a, b, None, true, true))
        None =>
          match intro_quantified_goal(state, prelude, g, name) {
            Ok(next) => keep_one(next)
            Err(e) => Err(e)
          }
      }
    Split =>
      match prop_dest_and(state, prelude, g.concl) {
        Some((a, b)) => {
          let and_full = g.concl
          let (oh, ol, obp, oip, orc) = copy_goal_shape(g)
          let g1 = PendingGoal::{
            hyps: oh.copy(),
            concl: a,
            locals: ol.copy(),
            branch_path: child_branch_path(obp, 1),
            imp_prefix: oip.copy(),
            refine_chain: orc.copy(),
            split_role: SplitLeft(and_full),
            or_ctx: g.or_ctx,
          }
          let g2 = PendingGoal::{
            hyps: oh,
            concl: b,
            locals: ol,
            branch_path: child_branch_path(obp, 2),
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
          let (oh, ol, obp, oip, orc) = copy_goal_shape(g)
          keep_one(PendingGoal::{
            hyps: oh,
            concl: a,
            locals: ol,
            branch_path: child_branch_path(obp, 1),
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
          let (oh, ol, obp, oip, orc) = copy_goal_shape(g)
          keep_one(PendingGoal::{
            hyps: oh,
            concl: b,
            locals: ol,
            branch_path: child_branch_path(obp, 1),
            imp_prefix: oip,
            refine_chain: orc,
            split_role: g.split_role,
            or_ctx: OrPendingRight(g.concl, al),
          })
        }
        None => Err(GoalShapeMismatch("right requires a disjunction goal"))
      }
    Apply(name) =>
      match apply_accept_name(state, prelude, g, name) {
        Ok(accepted) => Ok(apply_acceptance_state(ps.root_goal, rest, accepted))
        Err(e) => Err(e)
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
