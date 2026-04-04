///|
/// Minimal bool-facing wrapper over kernel ASSUME.
pub fn logic_assume(
  state : KernelState,
  prop : Term,
) -> Result[Thm, LogicError] {
  assume_checked(state, prop)
}

///|
pub fn logic_add_assum(
  state : KernelState,
  hyp : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  add_assum_checked(state, hyp, th)
}
