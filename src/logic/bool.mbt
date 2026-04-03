///|
/// Minimal bool-facing wrapper over kernel ASSUME.
pub fn logic_assume(
  state : KernelState,
  prop : Term,
) -> Result[Thm, LogicError] {
  assume_checked(state, prop)
}

///|
/// Phase readiness probe.
pub fn logic_bool_phase0_ready() -> Bool {
  true
}
