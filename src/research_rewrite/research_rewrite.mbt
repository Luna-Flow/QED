///|
pub enum ConnectorKind {
  Not
  Imp
  And
  Or
}

///|
pub enum RewriteDirection {
  LeftToRight
  RightToLeft
}

///|
pub enum RewriteSiteStep {
  CombFun
  CombArg
  AbsBody
}

///|
pub enum RewriteWitness {
  LocalEquality(String)
  ExplicitTheorem(Thm)
  CanonicalUnfold(ConnectorKind)
  BetaNormalization
}

///|
pub struct RewriteRequest {
  witness : RewriteWitness
  direction : RewriteDirection
  site : Array[RewriteSiteStep]
}

///|
pub enum ReplayStepKind {
  ResolveWitness
  Symmetry
  Congruence
  Unfold
  BetaNormalize
}

///|
pub struct ReplaySegment {
  request : RewriteRequest
  before_concl : Term
  after_concl : Term
  steps : Array[ReplayStepKind]
}

///|
pub struct ReplayObligation {
  before_concl : Term
  after_concl : Term
  segments : Array[ReplaySegment]
}

///|
pub enum RewriteResult {
  Rewritten(Term, ReplayObligation)
  NoChange
  HonestFailure(String)
}

///|
pub struct SimplifyConfig {
  step_limit : Int
  allow_unfold : Bool
  allow_beta : Bool
  rewrite_requests : Array[RewriteRequest]
}

///|
pub fn research_rewrite_request(
  witness : RewriteWitness,
  direction : RewriteDirection,
  site : Array[RewriteSiteStep],
) -> RewriteRequest {
  RewriteRequest::{ witness, direction, site }
}

///|
pub fn research_local_equality(name : String) -> RewriteWitness {
  LocalEquality(name)
}

///|
pub fn research_explicit_theorem(th : Thm) -> RewriteWitness {
  ExplicitTheorem(th)
}

///|
pub fn research_canonical_unfold_not() -> RewriteWitness {
  CanonicalUnfold(Not)
}

///|
pub fn research_canonical_unfold_imp() -> RewriteWitness {
  CanonicalUnfold(Imp)
}

///|
pub fn research_canonical_unfold_and() -> RewriteWitness {
  CanonicalUnfold(And)
}

///|
pub fn research_canonical_unfold_or() -> RewriteWitness {
  CanonicalUnfold(Or)
}

///|
pub fn research_beta_normalization() -> RewriteWitness {
  BetaNormalization
}

///|
pub fn research_left_to_right() -> RewriteDirection {
  LeftToRight
}

///|
pub fn research_right_to_left() -> RewriteDirection {
  RightToLeft
}

///|
pub fn research_site_comb_fun() -> RewriteSiteStep {
  CombFun
}

///|
pub fn research_site_comb_arg() -> RewriteSiteStep {
  CombArg
}

///|
pub fn research_site_abs_body() -> RewriteSiteStep {
  AbsBody
}

///|
pub fn research_replay_segment(
  request : RewriteRequest,
  before_concl : Term,
  after_concl : Term,
  steps : Array[ReplayStepKind],
) -> ReplaySegment {
  ReplaySegment::{ request, before_concl, after_concl, steps }
}

///|
pub fn research_replay_obligation(
  before_concl : Term,
  after_concl : Term,
  segments : Array[ReplaySegment],
) -> ReplayObligation {
  ReplayObligation::{ before_concl, after_concl, segments }
}

///|
pub fn research_simplify_config(
  step_limit : Int,
  allow_unfold : Bool,
  allow_beta : Bool,
  rewrite_requests : Array[RewriteRequest],
) -> SimplifyConfig {
  SimplifyConfig::{ step_limit, allow_unfold, allow_beta, rewrite_requests }
}

///|
pub fn research_step_name(step : ReplayStepKind) -> String {
  match step {
    ResolveWitness => "ResolveWitness"
    Symmetry => "Symmetry"
    Congruence => "Congruence"
    Unfold => "Unfold"
    BetaNormalize => "BetaNormalize"
  }
}

///|
priv enum RewriteBuildError {
  Honest(String)
  Logic(LogicError)
}

///|
priv enum RewriteCrumb {
  InCombFun(Term)
  InCombArg(Term)
}

///|
fn research_type_mismatch() -> LogicError {
  match
    mk_eq(
      @kernel.mk_var("_rr_bool", bool_ty()),
      @kernel.mk_var("_rr_other", mk_tyvar("_RR")),
    ) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn failure_to_logic_error(err : RewriteBuildError) -> LogicError {
  match err {
    Honest(_) => research_type_mismatch()
    Logic(e) => e
  }
}

///|
fn term_matches(lhs : Term, rhs : Term) -> Bool {
  term_logical_eq(lhs, rhs) || term_alpha_eq(lhs, rhs)
}

///|
fn replay_step_eq(lhs : ReplayStepKind, rhs : ReplayStepKind) -> Bool {
  match (lhs, rhs) {
    (ResolveWitness, ResolveWitness) => true
    (Symmetry, Symmetry) => true
    (Congruence, Congruence) => true
    (Unfold, Unfold) => true
    (BetaNormalize, BetaNormalize) => true
    _ => false
  }
}

///|
fn replay_steps_eq(
  lhs : Array[ReplayStepKind],
  rhs : Array[ReplayStepKind],
) -> Bool {
  if lhs.length() != rhs.length() {
    return false
  }
  let mut i = 0
  while i < lhs.length() {
    if !replay_step_eq(lhs[i], rhs[i]) {
      return false
    }
    i = i + 1
  }
  true
}

///|
fn append_step(
  steps : Array[ReplayStepKind],
  step : ReplayStepKind,
) -> Array[ReplayStepKind] {
  let out = steps.copy()
  out.push(step)
  out
}

///|
fn require_bool_concl(concl : Term) -> Result[Unit, RewriteBuildError] {
  match type_of(concl) {
    Some(ty) =>
      if ty_eq(ty, bool_ty()) {
        Ok(())
      } else {
        Err(Honest("research prototype only accepts bool-typed conclusions"))
      }
    None => Err(Honest("research prototype received an ill-typed conclusion"))
  }
}

///|
fn resolve_local_term(locals : Array[(String, Term)], name : String) -> Term? {
  let mut i = locals.length()
  while i > 0 {
    i = i - 1
    let (local_name, local_term) = locals[i]
    if local_name == name {
      return Some(local_term)
    }
  }
  None
}

///|
fn site_tail(site : Array[RewriteSiteStep]) -> Array[RewriteSiteStep] {
  let out : Array[RewriteSiteStep] = []
  let mut i = 1
  while i < site.length() {
    out.push(site[i])
    i = i + 1
  }
  out
}

///|
fn prepend_crumb(
  crumb : RewriteCrumb,
  crumbs : Array[RewriteCrumb],
) -> Array[RewriteCrumb] {
  let out : Array[RewriteCrumb] = [crumb]
  for item in crumbs {
    out.push(item)
  }
  out
}

///|
fn locate_focus(
  term : Term,
  site : Array[RewriteSiteStep],
) -> Result[(Term, Array[RewriteCrumb]), RewriteBuildError] {
  if site.length() == 0 {
    Ok((term, []))
  } else {
    let rest = site_tail(site)
    match site[0] {
      CombFun =>
        match dest_comb(term) {
          Some((fn_term, arg_term)) =>
            match locate_focus(fn_term, rest) {
              Ok((focus, crumbs)) =>
                Ok((focus, prepend_crumb(InCombFun(arg_term), crumbs)))
              Err(e) => Err(e)
            }
          None => Err(Honest("rewrite site expected a function application"))
        }
      CombArg =>
        match dest_comb(term) {
          Some((fn_term, arg_term)) =>
            match locate_focus(arg_term, rest) {
              Ok((focus, crumbs)) =>
                Ok((focus, prepend_crumb(InCombArg(fn_term), crumbs)))
              Err(e) => Err(e)
            }
          None => Err(Honest("rewrite site expected a function application"))
        }
      AbsBody =>
        match dest_abs(term) {
          Some(_) => Err(Honest("AbsBody rewrite is unsupported in G2"))
          None => Err(Honest("rewrite site expected a lambda abstraction"))
        }
    }
  }
}

///|
fn dest_app_spine(term : Term) -> (Term, Array[Term]) {
  let args : Array[Term] = []
  let mut head = term
  while true {
    match dest_comb(head) {
      Some((fn_term, arg_term)) => {
        args.push(arg_term)
        head = fn_term
      }
      None => break
    }
  }
  let out : Array[Term] = []
  let mut i = args.length()
  while i > 0 {
    i = i - 1
    out.push(args[i])
  }
  (head, out)
}

///|
fn extract_eq_sides(th : Thm) -> Result[(Term, Term), RewriteBuildError] {
  let concl = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  match dest_eq(concl) {
    Ok(v) => Ok(v)
    Err(_) => Err(Honest("rewrite witness must conclude an equality"))
  }
}

///|
fn orient_theorem(
  state : KernelState,
  th : Thm,
  direction : RewriteDirection,
  steps : Array[ReplayStepKind],
) -> Result[(Thm, Term, Term, Array[ReplayStepKind]), RewriteBuildError] {
  let oriented = match direction {
    LeftToRight => th
    RightToLeft =>
      match logic_eq_sym(state, th) {
        Ok(v) => v
        Err(e) => return Err(Logic(e))
      }
  }
  let steps2 = match direction {
    LeftToRight => steps
    RightToLeft => append_step(steps, Symmetry)
  }
  match extract_eq_sides(oriented) {
    Ok((lhs, rhs)) => Ok((oriented, lhs, rhs, steps2))
    Err(e) => Err(e)
  }
}

///|
fn explicit_witness_theorem(
  state : KernelState,
  locals : Array[(String, Term)],
  witness : RewriteWitness,
  direction : RewriteDirection,
) -> Result[(Thm, Term, Term, Array[ReplayStepKind]), RewriteBuildError] {
  match witness {
    LocalEquality(name) =>
      match resolve_local_term(locals, name) {
        Some(term) =>
          match logic_assume(state, term) {
            Ok(th) => orient_theorem(state, th, direction, [ResolveWitness])
            Err(e) => Err(Logic(e))
          }
        None => Err(Honest("unknown local equality: " + name))
      }
    ExplicitTheorem(th) =>
      orient_theorem(state, th, direction, [ResolveWitness])
    _ =>
      Err(Honest("rewrite request does not carry an explicit equality witness"))
  }
}

///|
fn connector_arity(kind : ConnectorKind) -> Int {
  match kind {
    Not => 1
    Imp => 2
    And => 2
    Or => 2
  }
}

///|
fn connector_definition_theorem(
  state : KernelState,
  prelude : PropPrelude,
  kind : ConnectorKind,
) -> Result[Thm, RewriteBuildError] {
  match kind {
    Not =>
      match logic_prop_def_not(state, prelude) {
        Ok(v) => Ok(v)
        Err(_) =>
          Err(
            Honest(
              "canonical not definition is unavailable in the current state",
            ),
          )
      }
    Imp =>
      match logic_prop_def_imp(state, prelude) {
        Ok(v) => Ok(v)
        Err(_) =>
          Err(
            Honest(
              "canonical imp definition is unavailable in the current state",
            ),
          )
      }
    And =>
      match logic_prop_def_and(state, prelude) {
        Ok(v) => Ok(v)
        Err(_) =>
          Err(
            Honest(
              "canonical and definition is unavailable in the current state",
            ),
          )
      }
    Or =>
      match logic_prop_def_or(state, prelude) {
        Ok(v) => Ok(v)
        Err(_) =>
          Err(
            Honest(
              "canonical or definition is unavailable in the current state",
            ),
          )
      }
  }
}

///|
fn apply_definition_to_args(
  state : KernelState,
  def_th : Thm,
  args : Array[Term],
) -> Result[Thm, RewriteBuildError] {
  match args.length() {
    0 => Ok(def_th)
    1 =>
      match logic_apply_fun_eq(state, def_th, args[0]) {
        Ok(v) => Ok(v)
        Err(e) => Err(Logic(e))
      }
    2 =>
      match logic_apply_fun_eq2(state, def_th, args[0], args[1]) {
        Ok(v) => Ok(v)
        Err(e) => Err(Logic(e))
      }
    _ =>
      Err(
        Honest(
          "canonical unfold only supports unary/binary proposition connectors",
        ),
      )
  }
}

///|
fn canonical_unfold_equality(
  state : KernelState,
  prelude : PropPrelude,
  focus : Term,
  kind : ConnectorKind,
  direction : RewriteDirection,
) -> Result[(Thm, Term, Array[ReplayStepKind]), RewriteBuildError] {
  match direction {
    RightToLeft => return Err(Honest("canonical fold is unsupported in G2"))
    LeftToRight => ()
  }
  let def_th = match connector_definition_theorem(state, prelude, kind) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let def_lhs = match logic_prop_def_lhs(def_th) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let (head, args) = dest_app_spine(focus)
  if !term_matches(head, def_lhs) {
    return Err(Honest("canonical unfold requires a matching connector head"))
  }
  if args.length() != connector_arity(kind) {
    return Err(Honest("canonical unfold arity mismatch"))
  }
  let th_applied = match apply_definition_to_args(state, def_th, args) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_norm = match research_beta_normalize_eq_full(state, th_applied) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match extract_eq_sides(th_norm) {
    Ok((lhs, rhs)) =>
      if term_matches(lhs, focus) {
        Ok((th_norm, rhs, [Unfold, BetaNormalize]))
      } else {
        Err(Honest("canonical unfold did not replay to the requested focus"))
      }
    Err(e) => Err(e)
  }
}

///|
fn research_beta_redex_at(
  state : KernelState,
  term : Term,
) -> Result[Thm, RewriteBuildError] {
  match logic_beta_rule(state, term) {
    Ok(th) => return Ok(th)
    Err(NotTrivialBetaRedex) => ()
    Err(e) => return Err(Logic(e))
  }
  match dest_comb(term) {
    Some((fn_term, arg_term)) =>
      match research_beta_redex_at(state, fn_term) {
        Ok(th_fn) => {
          let th_arg = match logic_refl(state, arg_term) {
            Ok(v) => v
            Err(e) => return Err(Logic(e))
          }
          match logic_mk_comb_rule(state, th_fn, th_arg) {
            Ok(v) => Ok(v)
            Err(e) => Err(Logic(e))
          }
        }
        Err(Honest(_)) =>
          match research_beta_redex_at(state, arg_term) {
            Ok(th_arg) => {
              let th_fn = match logic_refl(state, fn_term) {
                Ok(v) => v
                Err(e) => return Err(Logic(e))
              }
              match logic_mk_comb_rule(state, th_fn, th_arg) {
                Ok(v) => Ok(v)
                Err(e) => Err(Logic(e))
              }
            }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    None => Err(Honest("no beta redex at requested focus"))
  }
}

///|
fn research_beta_normalize_eq_full(
  state : KernelState,
  th_eq : Thm,
) -> Result[Thm, RewriteBuildError] {
  let mut cur = th_eq
  let mut steps = 0
  while steps < 512 {
    let rhs = match extract_eq_sides(cur) {
      Ok((_, term)) => term
      Err(e) => return Err(e)
    }
    match research_beta_redex_at(state, rhs) {
      Ok(th_beta) => {
        cur = match logic_trans(state, cur, th_beta) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
        steps = steps + 1
      }
      Err(Honest(_)) => return Ok(cur)
      Err(e) => return Err(e)
    }
  }
  Ok(cur)
}

///|
fn beta_normalization_equality(
  state : KernelState,
  focus : Term,
  direction : RewriteDirection,
) -> Result[(Thm, Term, Array[ReplayStepKind]), RewriteBuildError] {
  match direction {
    RightToLeft => return Err(Honest("beta expansion is unsupported in G2"))
    LeftToRight => ()
  }
  let th_same = match logic_refl(state, focus) {
    Ok(v) => v
    Err(e) => return Err(Logic(e))
  }
  let th_norm = match research_beta_normalize_eq_full(state, th_same) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match extract_eq_sides(th_norm) {
    Ok((lhs, rhs)) =>
      if term_matches(lhs, focus) {
        Ok((th_norm, rhs, [BetaNormalize]))
      } else {
        Err(Honest("beta normalization did not replay to the requested focus"))
      }
    Err(e) => Err(e)
  }
}

///|
fn focus_equality(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  focus : Term,
  request : RewriteRequest,
) -> Result[(Thm, Term, Array[ReplayStepKind]), RewriteBuildError] {
  match request.witness {
    LocalEquality(_) | ExplicitTheorem(_) =>
      match
        explicit_witness_theorem(
          state,
          locals,
          request.witness,
          request.direction,
        ) {
        Ok((th, lhs, rhs, steps)) =>
          if term_matches(lhs, focus) {
            Ok((th, rhs, steps))
          } else {
            Err(Honest("rewrite witness does not match the requested focus"))
          }
        Err(e) => Err(e)
      }
    CanonicalUnfold(kind) =>
      canonical_unfold_equality(state, prelude, focus, kind, request.direction)
    BetaNormalization =>
      beta_normalization_equality(state, focus, request.direction)
  }
}

///|
fn lift_focus_to_root(
  state : KernelState,
  base_th : Thm,
  crumbs : Array[RewriteCrumb],
  steps : Array[ReplayStepKind],
) -> Result[(Thm, Array[ReplayStepKind]), RewriteBuildError] {
  let mut th = base_th
  let out_steps = steps
  let mut i = crumbs.length()
  while i > 0 {
    i = i - 1
    match crumbs[i] {
      InCombFun(arg_term) => {
        let th_arg = match logic_refl(state, arg_term) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
        th = match logic_mk_comb_rule(state, th, th_arg) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
      }
      InCombArg(fn_term) => {
        let th_fn = match logic_refl(state, fn_term) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
        th = match logic_mk_comb_rule(state, th_fn, th) {
          Ok(v) => v
          Err(e) => return Err(Logic(e))
        }
      }
    }
    out_steps.push(Congruence)
  }
  Ok((th, out_steps))
}

///|
fn build_segment(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  concl : Term,
  request : RewriteRequest,
) -> Result[ReplaySegment?, RewriteBuildError] {
  let _ = match require_bool_concl(concl) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (focus, crumbs) = match locate_focus(concl, request.site) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (focus_th, _focus_after, base_steps) = match
    focus_equality(state, prelude, locals, focus, request) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (root_th, root_steps) = match
    lift_focus_to_root(state, focus_th, crumbs, base_steps) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (lhs, rhs) = match extract_eq_sides(root_th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_matches(lhs, concl) {
    return Err(Honest("replay did not reconstruct the requested conclusion"))
  }
  if term_matches(rhs, concl) {
    Ok(None)
  } else {
    Ok(
      Some(ReplaySegment::{
        request,
        before_concl: concl,
        after_concl: rhs,
        steps: root_steps,
      }),
    )
  }
}

///|
fn attempt_auto_unfold(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  concl : Term,
) -> ReplaySegment? {
  let requests : Array[RewriteRequest] = [
    RewriteRequest::{
      witness: CanonicalUnfold(Not),
      direction: LeftToRight,
      site: [],
    },
    RewriteRequest::{
      witness: CanonicalUnfold(Imp),
      direction: LeftToRight,
      site: [],
    },
    RewriteRequest::{
      witness: CanonicalUnfold(And),
      direction: LeftToRight,
      site: [],
    },
    RewriteRequest::{
      witness: CanonicalUnfold(Or),
      direction: LeftToRight,
      site: [],
    },
  ]
  for req in requests {
    match build_segment(state, prelude, locals, concl, req) {
      Ok(Some(seg)) => return Some(seg)
      _ => ()
    }
  }
  None
}

///|
fn attempt_auto_beta(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  concl : Term,
) -> ReplaySegment? {
  let req = RewriteRequest::{
    witness: BetaNormalization,
    direction: LeftToRight,
    site: [],
  }
  match build_segment(state, prelude, locals, concl, req) {
    Ok(Some(seg)) => Some(seg)
    _ => None
  }
}

///|
fn push_segment_with_limit(
  segments : Array[ReplaySegment],
  seg : ReplaySegment,
  used : Int,
  limit : Int,
) -> Result[(Array[ReplaySegment], Int), RewriteBuildError] {
  if used >= limit {
    Err(Honest("step limit exceeded"))
  } else {
    let out = segments.copy()
    out.push(seg)
    Ok((out, used + 1))
  }
}

///|
fn failure_message(err : RewriteBuildError) -> String {
  match err {
    Honest(msg) => msg
    Logic(_) => "checked replay failed under current helper constraints"
  }
}

///|
pub fn research_rewrite_term_concl(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  concl : Term,
  request : RewriteRequest,
) -> RewriteResult {
  match build_segment(state, prelude, locals, concl, request) {
    Ok(Some(seg)) =>
      Rewritten(seg.after_concl, ReplayObligation::{
        before_concl: concl,
        after_concl: seg.after_concl,
        segments: [seg],
      })
    Ok(None) => NoChange
    Err(e) => HonestFailure(failure_message(e))
  }
}

///|
pub fn research_validate_replay_obligation(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  obligation : ReplayObligation,
) -> Result[Unit, LogicError] {
  let _ = match require_bool_concl(obligation.before_concl) {
    Ok(v) => v
    Err(e) => return Err(failure_to_logic_error(e))
  }
  let mut current = obligation.before_concl
  for seg in obligation.segments {
    if !term_matches(seg.before_concl, current) {
      return Err(research_type_mismatch())
    }
    match build_segment(state, prelude, locals, current, seg.request) {
      Ok(Some(built)) =>
        if term_matches(built.after_concl, seg.after_concl) &&
          replay_steps_eq(built.steps, seg.steps) {
          current = seg.after_concl
        } else {
          return Err(research_type_mismatch())
        }
      Ok(None) => return Err(research_type_mismatch())
      Err(e) => return Err(failure_to_logic_error(e))
    }
  }
  if term_matches(current, obligation.after_concl) {
    Ok(())
  } else {
    Err(research_type_mismatch())
  }
}

///|
pub fn research_simplify_term_concl(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  concl : Term,
  cfg : SimplifyConfig,
) -> RewriteResult {
  let _ = match require_bool_concl(concl) {
    Ok(v) => v
    Err(e) => return HonestFailure(failure_message(e))
  }
  if cfg.step_limit < 0 {
    return HonestFailure("step limit must be non-negative")
  }
  let mut current = concl
  let mut segments : Array[ReplaySegment] = []
  let mut used = 0
  while true {
    let mut changed = false
    if cfg.allow_unfold {
      match attempt_auto_unfold(state, prelude, locals, current) {
        Some(seg) =>
          match push_segment_with_limit(segments, seg, used, cfg.step_limit) {
            Ok((next_segments, next_used)) => {
              current = next_segments[next_segments.length() - 1].after_concl
              segments = next_segments
              used = next_used
              changed = true
            }
            Err(e) => return HonestFailure(failure_message(e))
          }
        None => ()
      }
    }
    if cfg.allow_beta {
      match attempt_auto_beta(state, prelude, locals, current) {
        Some(seg) =>
          match push_segment_with_limit(segments, seg, used, cfg.step_limit) {
            Ok((next_segments, next_used)) => {
              current = next_segments[next_segments.length() - 1].after_concl
              segments = next_segments
              used = next_used
              changed = true
            }
            Err(e) => return HonestFailure(failure_message(e))
          }
        None => ()
      }
    }
    for req in cfg.rewrite_requests {
      match build_segment(state, prelude, locals, current, req) {
        Ok(Some(seg)) =>
          match push_segment_with_limit(segments, seg, used, cfg.step_limit) {
            Ok((next_segments, next_used)) => {
              current = next_segments[next_segments.length() - 1].after_concl
              segments = next_segments
              used = next_used
              changed = true
            }
            Err(e) => return HonestFailure(failure_message(e))
          }
        Ok(None) => ()
        Err(Honest(_)) => ()
        Err(e) => return HonestFailure(failure_message(e))
      }
    }
    if cfg.allow_beta {
      match attempt_auto_beta(state, prelude, locals, current) {
        Some(seg) =>
          match push_segment_with_limit(segments, seg, used, cfg.step_limit) {
            Ok((next_segments, next_used)) => {
              current = next_segments[next_segments.length() - 1].after_concl
              segments = next_segments
              used = next_used
              changed = true
            }
            Err(e) => return HonestFailure(failure_message(e))
          }
        None => ()
      }
    }
    if !changed {
      break
    }
  }
  if segments.length() == 0 {
    NoChange
  } else {
    Rewritten(current, ReplayObligation::{
      before_concl: concl,
      after_concl: current,
      segments,
    })
  }
}
