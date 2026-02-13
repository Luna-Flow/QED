///|
/// Minimal global signature registry for kernel-level constant identities.
pub enum GlobalSig {
  Sig(Array[(String, HolType)])
}

///|
pub fn empty_sig() -> GlobalSig {
  Sig([])
}

///|
pub fn sig_has_const(sig : GlobalSig, name : String) -> Bool {
  match sig {
    Sig(entries) =>
      entries.any(fn(entry) {
        let (n, _) = entry
        n == name
      })
  }
}

///|
pub fn sig_lookup_const(sig : GlobalSig, name : String) -> HolType? {
  match sig {
    Sig(entries) => {
      for entry in entries {
        let (n, ty) = entry
        if n == name {
          return Some(ty)
        }
      }
      None
    }
  }
}

///|
pub fn sig_add_const(
  sig : GlobalSig,
  name : String,
  ty : HolType,
) -> GlobalSig? {
  if sig_has_const(sig, name) {
    None
  } else {
    match sig {
      Sig(entries) => {
        let out = entries.copy()
        out.push((name, ty))
        Some(Sig(out))
      }
    }
  }
}

///|
pub fn sig_add_const_idempotent(
  sig : GlobalSig,
  name : String,
  ty : HolType,
) -> GlobalSig? {
  match sig_lookup_const(sig, name) {
    Some(existing) =>
      if hol_type_to_string(existing) == hol_type_to_string(ty) {
        Some(sig)
      } else {
        None
      }
    None => sig_add_const(sig, name, ty)
  }
}

///|
pub fn sig_mk_const(sig : GlobalSig, name : String) -> Term? {
  match sig_lookup_const(sig, name) {
    Some(ty) => Some(mk_const(name, ty))
    None => None
  }
}

///|
pub fn sig_define_const(
  sig : GlobalSig,
  name : String,
  rhs : Term,
) -> (GlobalSig, Term)? {
  let ty = type_of(rhs)
  match sig_add_const_idempotent(sig, name, ty) {
    Some(sig2) =>
      match sig_mk_const(sig2, name) {
        Some(c) => Some((sig2, mk_eq(c, rhs)))
        None => None
      }
    None => None
  }
}
