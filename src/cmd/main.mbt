///|
/// Minimal demo path that exercises logic + tactics integration.
pub fn run_cli_phase0() -> Int {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let st1 = match @kernel.ks_add_const(st0, "P", bool) {
    Ok(st) => st
    Err(_) => return 1
  }
  let p = match @kernel.ks_mk_const(st1, "P") {
    Ok(v) => v
    Err(_) => return 1
  }
  let goal = @tactics.mk_goal([], p)
  match @tactics.solve_by_assume(st1, goal) {
    Ok(_) => 0
    Err(_) => 1
  }
}
