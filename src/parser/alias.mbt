///|
using @kernel {
  type HolType,
  type KernelState,
  type LogicError,
  type SigError,
  type Term,
  type Thm,
  bool_ty,
  empty_kernel_state,
  ind_ty,
  mk_eq,
  mk_tyvar,
  mk_tyapp,
  mk_var,
  fun_ty,
  ks_add_const,
  ks_define_const_thm,
  ks_mk_const,
  ks_mk_const_instance,
  mk_abs,
  type_of,
}

///|
using @elab {
  type ElabCtx,
  type ElabError,
  type RTerm,
  elab_app,
  elab_eq,
  elab_ctx_from_locals,
  elab_err_core_typing_failure,
  elab_err_invalid_const_instance,
  elab_err_scope_resolution_mismatch,
  elab_err_unknown_const,
  elab_err_unknown_name,
  elab_lower_to_term,
  elab_resolve_named_term,
  elab_resolve_app,
  elab_resolve_eq,
  elab_resolve_name,
}

///|
using @tactics {type Goal, mk_goal}

///|
using @logic {
  default_prop_prelude,
  prop_mk_and,
  prop_mk_imp,
  prop_mk_not,
  prop_mk_or,
}
