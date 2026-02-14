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
pub fn ind_ty() -> HolType {
  TyApp("ind", [])
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

///|
pub fn ty_eq(t1 : HolType, t2 : HolType) -> Bool {
  match (t1, t2) {
    (TyVal(n1), TyVal(n2)) => n1 == n2
    (TyApp(c1, a1), TyApp(c2, a2)) =>
      if c1 != c2 || a1.length() != a2.length() {
        false
      } else {
        let mut i = 0
        while i < a1.length() {
          if !ty_eq(a1[i], a2[i]) {
            return false
          }
          i = i + 1
        }
        true
      }
    _ => false
  }
}

///|
fn lookup_ty_subst(subst : Array[(String, HolType)], key : String) -> HolType? {
  for item in subst {
    let (k, v) = item
    if k == key {
      return Some(v)
    }
  }
  None
}

///|
pub fn has_duplicate_ty_subst_keys(subst : Array[(String, HolType)]) -> Bool {
  let seen : Array[String] = []
  for item in subst {
    let (k, _) = item
    if seen.contains(k) {
      return true
    }
    seen.push(k)
  }
  false
}

///|
pub fn type_subst(subst : Array[(String, HolType)], ty : HolType) -> HolType? {
  if has_duplicate_ty_subst_keys(subst) {
    return None
  }
  Some(type_subst_unsafe(subst, ty))
}

///|
pub fn type_subst_unsafe(
  subst : Array[(String, HolType)],
  ty : HolType,
) -> HolType {
  match ty {
    TyVal(name) =>
      match lookup_ty_subst(subst, name) {
        Some(out) => out
        None => ty
      }
    TyApp(tycon, args) =>
      TyApp(tycon, args.map(fn(arg) { type_subst_unsafe(subst, arg) }))
  }
}

///|
fn collect_tyvars(ty : HolType, out : Array[String]) -> Unit {
  match ty {
    TyVal(name) => if !out.contains(name) { out.push(name) }
    TyApp(_, args) => args.each(fn(arg) { collect_tyvars(arg, out) })
  }
}

///|
pub fn tyvars(ty : HolType) -> Array[String] {
  let out : Array[String] = []
  collect_tyvars(ty, out)
  out
}

///|
pub fn tyvars_subset(lhs : HolType, rhs : HolType) -> Bool {
  let a = tyvars(lhs)
  let b = tyvars(rhs)
  a.all(fn(x) { b.contains(x) })
}

///|
fn collect_instance_bindings(
  schema : HolType,
  instance : HolType,
  env : Array[(String, HolType)],
) -> Bool {
  match schema {
    TyVal(name) =>
      match lookup_ty_subst(env, name) {
        Some(bound) => ty_eq(bound, instance)
        None => {
          env.push((name, instance))
          true
        }
      }
    TyApp(s_con, s_args) =>
      match instance {
        TyApp(i_con, i_args) =>
          if s_con != i_con || s_args.length() != i_args.length() {
            false
          } else {
            let mut i = 0
            while i < s_args.length() {
              if !collect_instance_bindings(s_args[i], i_args[i], env) {
                return false
              }
              i = i + 1
            }
            true
          }
        _ => false
      }
  }
}

///|
/// Returns true when `instance` is an instance of `schema` under type substitution.
pub fn ty_is_instance_of(instance : HolType, schema : HolType) -> Bool {
  let env : Array[(String, HolType)] = []
  collect_instance_bindings(schema, instance, env)
}

///|
/// Pretty printer for debug and test output.
pub fn hol_type_to_string(ty : HolType) -> String {
  match ty {
    TyVal(name) => name
    TyApp(tycon, args) =>
      if args.length() == 0 {
        tycon
      } else {
        let rendered = args.map(fn(arg) { hol_type_to_string(arg) }).join(", ")
        tycon + "(" + rendered + ")"
      }
  }
}
