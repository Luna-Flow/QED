///|
/// Blackbox test package: full `using` union (main `alias.mbt` is not in scope here).
using @kernel {
  type ConstId,
  type DbTerm,
  type HolType,
  type Term,
  type KernelState,
  type SigError,
  type LogicError,
  bool_ty,
  mk_tyvar,
  mk_var,
  mk_eq,
  empty_kernel_state,
  ks_add_const,
  ks_push_scope,
  assume_checked,
  ks_mk_const,
  ks_mk_const_instance,
  ks_const_schema,
  ks_lookup_const_id,
  mk_comb,
  mk_abs,
  mk_const,
  mk_const_bound,
  type_of,
  is_bool_ty,
  hol_type_to_string,
  dest_fun_ty,
  dest_abs,
  dest_comb,
  dest_const,
  dest_eq,
  dest_var,
  fun_ty,
  to_db_term,
  term_alpha_eq,
  ty_eq,
  ty_is_instance_of,
  db_term_eq,
  ind_ty,
}

///|
test "alias keepalive for elab imports" {
  let _ : ConstId? = None
  let _ : DbTerm? = None
  let _ : HolType? = None
  let _ : Term? = None
  let _ : KernelState? = None
  let _ : SigError? = None
  let _ : LogicError? = None
  let _ = bool_ty
  let _ = mk_tyvar
  let _ = mk_var
  let _ = mk_eq
  let _ = empty_kernel_state
  let _ = ks_add_const
  let _ = ks_push_scope
  let _ = assume_checked
  let _ = ks_mk_const
  let _ = ks_mk_const_instance
  let _ = ks_const_schema
  let _ = ks_lookup_const_id
  let _ = mk_abs
  let _ = mk_const_bound
  let _ = type_of
  let _ = is_bool_ty
  let _ = hol_type_to_string
  let _ = dest_fun_ty
  let _ = dest_abs
  let _ = dest_comb
  let _ = dest_const
  let _ = dest_eq
  let _ = dest_var
  let _ = fun_ty
  let _ = to_db_term
  let _ = term_alpha_eq
  let _ = ty_eq
  let _ = ty_is_instance_of
  let _ = db_term_eq
  let _ = ind_ty
}
