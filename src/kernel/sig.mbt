///|
/// Minimal global signature registry for kernel-level constant identities.
pub enum GlobalSig {
  Sig(Array[Array[(String, HolType)]])
}

///|
pub enum SigError {
  DuplicateConstName
  ConstTypeConflict
  UnknownConst
  ScopeUnderflow
  InvalidConstRhs
}

///|
pub fn empty_sig() -> GlobalSig {
  Sig([[]])
}

///|
pub fn sig_push_scope(sig : GlobalSig) -> GlobalSig {
  match sig {
    Sig(scopes) => {
      let out = scopes.copy()
      out.push([])
      Sig(out)
    }
  }
}

///|
pub fn sig_pop_scope(sig : GlobalSig) -> GlobalSig? {
  match sig {
    Sig(scopes) =>
      if scopes.length() <= 1 {
        None
      } else {
        let out = scopes.copy()
        let _ = out.pop()
        Some(Sig(out))
      }
  }
}

///|
pub fn sig_pop_scope_e(sig : GlobalSig) -> Result[GlobalSig, SigError] {
  match sig_pop_scope(sig) {
    Some(sig2) => Ok(sig2)
    None => Err(ScopeUnderflow)
  }
}

///|
fn lookup_in_scope(scope : Array[(String, HolType)], name : String) -> HolType? {
  for entry in scope {
    let (n, ty) = entry
    if n == name {
      return Some(ty)
    }
  }
  None
}

///|
fn current_scope_lookup(sig : GlobalSig, name : String) -> HolType? {
  match sig {
    Sig(scopes) =>
      if scopes.length() == 0 {
        None
      } else {
        lookup_in_scope(scopes[scopes.length() - 1], name)
      }
  }
}

///|
pub fn sig_has_const(sig : GlobalSig, name : String) -> Bool {
  sig_lookup_const(sig, name) is Some(_)
}

///|
pub fn sig_lookup_const(sig : GlobalSig, name : String) -> HolType? {
  match sig {
    Sig(scopes) => {
      let mut i = scopes.length()
      while i > 0 {
        i = i - 1
        match lookup_in_scope(scopes[i], name) {
          Some(ty) => return Some(ty)
          None => ()
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
  match current_scope_lookup(sig, name) {
    Some(_) => None
    None =>
      match sig {
        Sig(scopes) =>
          if scopes.length() == 0 {
            None
          } else {
            let out = scopes.copy()
            let top = out[out.length() - 1].copy()
            top.push((name, ty))
            out[out.length() - 1] = top
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
  match current_scope_lookup(sig, name) {
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
pub fn sig_add_const_idempotent_e(
  sig : GlobalSig,
  name : String,
  ty : HolType,
) -> Result[GlobalSig, SigError] {
  match current_scope_lookup(sig, name) {
    Some(existing) =>
      if hol_type_to_string(existing) == hol_type_to_string(ty) {
        Ok(sig)
      } else {
        Err(ConstTypeConflict)
      }
    None =>
      match sig_add_const(sig, name, ty) {
        Some(sig2) => Ok(sig2)
        None => Err(DuplicateConstName)
      }
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
pub fn sig_mk_const_e(sig : GlobalSig, name : String) -> Result[Term, SigError] {
  match sig_lookup_const(sig, name) {
    Some(ty) => Ok(mk_const(name, ty))
    None => Err(UnknownConst)
  }
}

///|
pub fn sig_define_const(
  sig : GlobalSig,
  name : String,
  rhs : Term,
) -> (GlobalSig, Term)? {
  match type_of(rhs) {
    Some(ty) =>
      match sig_add_const_idempotent(sig, name, ty) {
        Some(sig2) =>
          match sig_mk_const(sig2, name) {
            Some(c) =>
              match mk_eq(c, rhs) {
                Some(eq) => Some((sig2, eq))
                None => None
              }
            None => None
          }
        None => None
      }
    None => None
  }
}

///|
pub fn sig_define_const_e(
  sig : GlobalSig,
  name : String,
  rhs : Term,
) -> Result[(GlobalSig, Term), SigError] {
  match type_of(rhs) {
    Some(ty) =>
      match sig_add_const_idempotent_e(sig, name, ty) {
        Ok(sig2) =>
          match sig_mk_const_e(sig2, name) {
            Ok(c) =>
              match mk_eq(c, rhs) {
                Some(eq) => Ok((sig2, eq))
                None => Err(InvalidConstRhs)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    None => Err(InvalidConstRhs)
  }
}
