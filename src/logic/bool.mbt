///|
/// Minimal bool-facing wrapper over kernel ASSUME.
pub fn logic_assume(
  state : @kernel.KernelState,
  prop : @kernel.Term,
) -> Result[@kernel.Thm, @kernel.LogicError] {
  @kernel.assume_checked(state, prop)
}

///|
/// Phase readiness probe.
pub fn logic_bool_phase0_ready() -> Bool {
  true
}
