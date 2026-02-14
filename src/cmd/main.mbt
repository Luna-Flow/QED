///|
/// Minimal demo path that exercises logic + tactics integration.
pub fn run_cli_phase0() -> Int {
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_const("P", bool)
  let goal = @tactics.mk_goal([], p)
  match @tactics.solve_by_assume(goal) {
    Ok(_) => 0
    Err(_) => 1
  }
}
