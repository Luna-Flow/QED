///|
/// HOL type representation used by the trusted kernel.
pub enum HolType {
  TyVal(String)
  TyApp(String, Array[HolType])
}

///|
/// Constructors
pub fn mk_tyvar(name : String) -> HolType {
  TyVal(name)
}

///|
pub fn mk_tyapp(tycon : String, args : Array[HolType]) -> HolType {
  TyApp(tycon, args)
}

///|
pub fn bool_ty() -> HolType {
  TyApp("bool", [])
}

///|
pub fn fun_ty(dom : HolType, cod : HolType) -> HolType {
  TyApp("fun", [dom, cod])
}

///|
/// Predicates
pub fn is_tyvar(ty : HolType) -> Bool {
  match ty {
    TyVal(_) => true
    _ => false
  }
}

///|
pub fn is_tyapp(ty : HolType) -> Bool {
  match ty {
    TyApp(_, _) => true
    _ => false
  }
}
