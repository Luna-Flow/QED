///|
/// Minimal demo path that exercises logic + tactics integration.
pub fn run_cli_phase0() -> Int {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = match ks_add_const(st0, "P", bool) {
    Ok(st) => st
    Err(_) => return 1
  }
  let p = match ks_mk_const(st1, "P") {
    Ok(v) => v
    Err(_) => return 1
  }
  let goal = mk_goal([], p)
  match solve_by_assume(st1, goal) {
    Ok(_) => 0
    Err(_) => 1
  }
}
