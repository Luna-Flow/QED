///|
fn alpha_mismatch_error() -> LogicError {
  let st = empty_kernel_state()
  let a = mk_tyvar("_A")
  let x = mk_var("_x", a)
  let y = mk_var("_y", a)
  let z = mk_var("_z", a)

  let eq_xy = match mk_eq(x, y) {
    Ok(v) => v
    Err(_) => panic()
  }
  let eq_zx = match mk_eq(z, x) {
    Ok(v) => v
    Err(_) => panic()
  }

  let th_xy = match logic_assume(st, eq_xy) {
    Ok(v) => v
    Err(_) => panic()
  }
  let th_zx = match logic_assume(st, eq_zx) {
    Ok(v) => v
    Err(_) => panic()
  }
  match logic_trans(st, th_xy, th_zx) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
/// Minimal tactic: solve current goal by assuming its conclusion.
pub fn solve_by_assume(
  state : KernelState,
  goal : Goal,
) -> Result[Thm, LogicError] {
  logic_assume(state, goal_concl(goal))
}

///|
pub fn solve_by_refl(
  state : KernelState,
  term : Term,
) -> Result[Thm, LogicError] {
  logic_refl(state, term)
}

///|
pub fn solve_by_trans(
  state : KernelState,
  th1 : Thm,
  th2 : Thm,
) -> Result[Thm, LogicError] {
  logic_trans(state, th1, th2)
}

///|
pub fn solve_by_hyp(
  state : KernelState,
  goal : Goal,
) -> Result[Thm, LogicError] {
  let concl = goal_concl(goal)
  for hyp in goal_hyps(goal) {
    if term_alpha_eq(hyp, concl) {
      return logic_assume(state, hyp)
    }
  }
  Err(alpha_mismatch_error())
}

///|
pub fn tactics_engine_phase0_ready() -> Bool {
  true
}
