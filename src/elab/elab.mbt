///|
fn type_mismatch_error() -> LogicError {
  let lhs = mk_var("_tm_lhs", bool_ty())
  let rhs = mk_var("_tm_rhs", mk_tyvar("_TM"))
  match mk_eq(lhs, rhs) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn not_bool_term_error() -> LogicError {
  let st = empty_kernel_state()
  let x = mk_var("_nb", mk_tyvar("_NB"))
  match assume_checked(st, x) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
pub fn elab_var(name : String, ty : HolType) -> Term {
  mk_var(name, ty)
}

///|
pub fn elab_const(state : KernelState, name : String) -> Result[Term, SigError] {
  ks_mk_const(state, name)
}

///|
pub fn elab_const_instance(
  state : KernelState,
  name : String,
  inst_ty : HolType,
) -> Result[Term, SigError] {
  ks_mk_const_instance(state, name, inst_ty)
}

///|
pub fn elab_app(f : Term, x : Term) -> Result[Term, LogicError] {
  let out = mk_comb(f, x)
  match type_of(out) {
    Some(_) => Ok(out)
    None => Err(type_mismatch_error())
  }
}

///|
pub fn elab_app2(f : Term, x : Term, y : Term) -> Result[Term, LogicError] {
  match elab_app(f, x) {
    Ok(fx) => elab_app(fx, y)
    Err(e) => Err(e)
  }
}

///|
pub fn elab_abs(
  name : String,
  ty : HolType,
  body : Term,
) -> Result[Term, LogicError] {
  let out = mk_abs(mk_var(name, ty), body)
  match type_of(out) {
    Some(_) => Ok(out)
    None => Err(type_mismatch_error())
  }
}

///|
pub fn elab_eq(lhs : Term, rhs : Term) -> Result[Term, LogicError] {
  mk_eq(lhs, rhs)
}

///|
pub fn elab_is_prop(term : Term) -> Bool {
  match type_of(term) {
    Some(ty) => is_bool_ty(ty)
    None => false
  }
}

///|
pub fn elab_require_prop(term : Term) -> Result[Term, LogicError] {
  match type_of(term) {
    Some(ty) =>
      if is_bool_ty(ty) {
        Ok(term)
      } else {
        Err(not_bool_term_error())
      }
    None => Err(type_mismatch_error())
  }
}

///|
pub fn elab_phase0_ready() -> Bool {
  true
}
