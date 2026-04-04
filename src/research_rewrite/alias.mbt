///|
/// Package-local aliases for the isolated rewrite/simplify research package.
using @kernel {
  type KernelState,
  type Term,
  type Thm,
  type LogicError,
  bool_ty,
  mk_tyvar,
  ty_eq,
  mk_eq,
  dest_comb,
  dest_abs,
  dest_eq,
  term_alpha_eq,
  term_logical_eq,
  thm_concl,
  type_of,
}

///|
using @logic {
  type PropPrelude,
  logic_assume,
  logic_refl,
  logic_eq_sym,
  logic_apply_fun_eq,
  logic_apply_fun_eq2,
  logic_mk_comb_rule,
  logic_beta_rule,
  logic_trans,
  logic_prop_def_imp,
  logic_prop_def_not,
  logic_prop_def_and,
  logic_prop_def_or,
  logic_prop_def_lhs,
}
