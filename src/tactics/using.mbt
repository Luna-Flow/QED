///|
using @kernel {
  type KernelState,
  type Thm,
  type Term,
  type LogicError,
  empty_kernel_state,
  mk_tyvar,
  mk_var,
  mk_eq,
  term_alpha_eq,
}

///|
using @logic {logic_assume, logic_trans, logic_refl}

///|
using @logic {
  type PropPrelude,
  prop_prelude_has_rule,
  prop_dest_imp,
  prop_dest_and,
  prop_dest_or,
}
