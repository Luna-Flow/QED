///|
/// Equality introduction through kernel REFL.
pub fn logic_refl(state : KernelState, term : Term) -> Result[Thm, LogicError] {
  refl_checked(state, term)
}

///|
/// Equality transitivity through kernel TRANS.
pub fn logic_trans(
  state : KernelState,
  th1 : Thm,
  th2 : Thm,
) -> Result[Thm, LogicError] {
  trans_checked(state, th1, th2)
}
