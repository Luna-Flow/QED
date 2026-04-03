///|
pub fn logic_mk_comb_rule(
  state : KernelState,
  th_fg : Thm,
  th_xy : Thm,
) -> Result[Thm, LogicError] {
  mk_comb_rule_checked(state, th_fg, th_xy)
}

///|
pub fn logic_abs_rule(
  state : KernelState,
  x : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  abs_rule_checked(state, x, th)
}

///|
pub fn logic_beta_rule(
  state : KernelState,
  term : Term,
) -> Result[Thm, LogicError] {
  beta_rule_checked(state, term)
}

///|
pub fn logic_eq_mp(
  state : KernelState,
  th_eq : Thm,
  th_p : Thm,
) -> Result[Thm, LogicError] {
  eq_mp_checked(state, th_eq, th_p)
}

///|
pub fn logic_deduct_antisym(
  state : KernelState,
  th1 : Thm,
  th2 : Thm,
) -> Result[Thm, LogicError] {
  deduct_antisym_rule_checked(state, th1, th2)
}

///|
pub fn logic_inst_type(
  state : KernelState,
  subst : Array[(String, HolType)],
  th : Thm,
) -> Result[Thm, LogicError] {
  inst_type(state, subst, th)
}

///|
pub fn logic_inst(
  state : KernelState,
  subst : Array[(Term, Term)],
  th : Thm,
) -> Result[Thm, LogicError] {
  inst_checked(state, subst, th)
}

///|
pub fn logic_rules_phase0_ready() -> Bool {
  true
}
