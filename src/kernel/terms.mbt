///|
/// HOL term representation used by the trusted kernel.
pub enum Term {
  Var(String, HolType)
  Const(String, HolType)
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
/// Returns the type of a term.
pub fn type_of(term : Term) -> HolType {
  match term {
    Var(_, ty) => ty
    Const(_, ty) => ty
  }
}

///|
pub fn kernel_terms_phase0_ready() -> Bool {
  true
}
