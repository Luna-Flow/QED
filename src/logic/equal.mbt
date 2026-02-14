///|
/// Equality introduction through kernel REFL.
pub fn logic_refl(
  state : @kernel.KernelState,
  term : @kernel.Term,
) -> Result[@kernel.Thm, @kernel.LogicError] {
  @kernel.refl_checked(state, term)
}

///|
/// Equality transitivity through kernel TRANS.
pub fn logic_trans(
  state : @kernel.KernelState,
  th1 : @kernel.Thm,
  th2 : @kernel.Thm,
) -> Result[@kernel.Thm, @kernel.LogicError] {
  @kernel.trans_checked(state, th1, th2)
}

///|
pub fn logic_equal_phase0_ready() -> Bool {
  true
}
