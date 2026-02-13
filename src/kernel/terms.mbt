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
/// Predicates
pub fn is_var(term : Term) -> Bool {
  match term {
    Var(_, _) => true
    _ => false
  }
}

///|
pub fn is_const(term : Term) -> Bool {
  match term {
    Const(_, _) => true
    _ => false
  }
}

///|
pub fn is_comb(term : Term) -> Bool {
  match term {
    Comb(_, _) => true
    _ => false
  }
}

///|
pub fn is_abs(term : Term) -> Bool {
  match term {
    Abs(_, _) => true
    _ => false
  }
}

///|
/// Destructors
pub fn dest_var(term : Term) -> (String, HolType)? {
  match term {
    Var(name, ty) => Some((name, ty))
    _ => None
  }
}

///|
pub fn dest_const(term : Term) -> (String, HolType)? {
  match term {
    Const(name, ty) => Some((name, ty))
    _ => None
  }
}

///|
pub fn dest_comb(term : Term) -> (Term, Term)? {
  match term {
    Comb(fn_term, arg_term) => Some((fn_term, arg_term))
    _ => None
  }
}

///|
pub fn dest_abs(term : Term) -> (Term, Term)? {
  match term {
    Abs(var_term, body) => Some((var_term, body))
    _ => None
  }
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
