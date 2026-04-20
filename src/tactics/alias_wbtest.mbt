///|
/// Whitebox test alias entry for tactics sources.
/// Keep shared wbtest-only imports here so each `_wbtest.mbt` stays small.
using @kernel {
  empty_kernel_state,
  bool_ty,
  ks_add_const,
  ks_mk_const,
  mk_abs,
  mk_comb,
  mk_eq,
  term_to_string,
}

///|
using @logic {
  default_prop_prelude,
  install_prop_prelude,
  prop_mk_imp,
  logic_add_assum,
  logic_abs_rule,
  logic_deduct_antisym,
  logic_prop_imp_intro_thm,
  logic_prop_or_intro_l_thm,
  logic_prop_truth_const_thm,
}
