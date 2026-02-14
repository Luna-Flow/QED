///|
/// Minimal tactic: solve current goal by assuming its conclusion.
pub fn solve_by_assume(goal : Goal) -> Result[@kernel.Thm, @kernel.LogicError] {
  @logic.logic_assume(goal_concl(goal))
}

///|
pub fn tactics_engine_phase0_ready() -> Bool {
  true
}
