///|
/// HOL term representation used by the trusted kernel.
pub enum Term {
  Var(String, HolType)
  Const(String, HolType)
  Comb(Term, Term)
  Abs(Term, Term)
}

///|
/// Constructors
pub fn mk_var(name : String, ty : HolType) -> Term {
  Var(name, ty)
}

///|
pub fn mk_const(name : String, ty : HolType) -> Term {
  Const(name, ty)
}

///|
pub fn mk_comb(fn_term : Term, arg_term : Term) -> Term {
  Comb(fn_term, arg_term)
}

///|
pub fn mk_abs(var_term : Term, body : Term) -> Term {
  Abs(var_term, body)
}

///|
/// Returns the type of a term.
pub fn type_of(term : Term) -> HolType {
  match term {
    Var(_, ty) => ty
    Const(_, ty) => ty
    Comb(fn_term, _) =>
      match type_of(fn_term) {
        TyApp("fun", [_, cod]) => cod
        _ => bool_ty()
      }
    Abs(var_term, body) => fun_ty(type_of(var_term), type_of(body))
  }
}

///|
pub fn kernel_terms_phase0_ready() -> Bool {
  true
}
