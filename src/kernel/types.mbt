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
/// Destructors
pub fn dest_tyapp(ty : HolType) -> (String, Array[HolType])? {
  match ty {
    TyApp(tycon, args) => Some((tycon, args))
    _ => None
  }
}

///|
pub fn dest_fun_ty(ty : HolType) -> (HolType, HolType)? {
  match ty {
    TyApp("fun", [dom, cod]) => Some((dom, cod))
    _ => None
  }
}

///|
pub fn is_bool_ty(ty : HolType) -> Bool {
  match ty {
    TyApp("bool", []) => true
    _ => false
  }
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
