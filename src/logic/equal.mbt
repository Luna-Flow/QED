///|
/// Equality introduction through kernel REFL.
pub fn logic_refl(
  term : @kernel.Term,
) -> Result[@kernel.Thm, @kernel.LogicError] {
  @kernel.refl(term)
}

///|
/// Equality transitivity through kernel TRANS.
pub fn logic_trans(
  th1 : @kernel.Thm,
  th2 : @kernel.Thm,
) -> Result[@kernel.Thm, @kernel.LogicError] {
  @kernel.trans(th1, th2)
}

///|
pub fn logic_equal_phase0_ready() -> Bool {
  true
}
