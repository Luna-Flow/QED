///|
/// Scoped constant signature used for name lookup.
pub enum GlobalSig {
  Sig(Array[Array[(String, HolType)]])
}

///|
/// Signature and admissibility errors.
pub suberror SigError {
  DuplicateConstName
  ConstTypeConflict
  UnknownConst
  ScopeUnderflow
  InvalidConstRhs
  ReservedSymbol
  DefinitionAlreadyExists
  DefinitionNotClosed
  DefinitionIsCyclic
  GhostTypeVariable
  TypeDefWitnessMissing
  TypeMismatch
}

///|
priv struct TheoryState {
  def_heads : Array[String]
  witnessed_tycons : Array[(String, Int)]
}

///|
struct KernelState {
  sig : GlobalSig
  theory : TheoryState
}

///|
fn is_reserved_symbol(name : String) -> Bool {
  name == "="
}

///|
fn is_builtin_tycon(name : String, arity : Int) -> Bool {
  (name == "bool" && arity == 0) || (name == "fun" && arity == 2)
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
  if is_reserved_symbol(name) {
    return None
  }
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
  if is_reserved_symbol(name) {
    return None
  }
  match current_scope_lookup(sig, name) {
    Some(existing) => if ty_eq(existing, ty) { Some(sig) } else { None }
    None => sig_add_const(sig, name, ty)
  }
}

///|
pub fn sig_add_const_idempotent_e(
  sig : GlobalSig,
  name : String,
  ty : HolType,
) -> Result[GlobalSig, SigError] {
  if is_reserved_symbol(name) {
    return Err(ReservedSymbol)
  }
  match current_scope_lookup(sig, name) {
    Some(existing) =>
      if ty_eq(existing, ty) {
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
  if is_reserved_symbol(name) {
    return None
  }
  match type_of(rhs) {
    Some(ty) =>
      match sig_add_const(sig, name, ty) {
        Some(sig2) =>
          match sig_mk_const(sig2, name) {
            Some(c) =>
              match mk_eq(c, rhs) {
                Ok(eq) => Some((sig2, eq))
                Err(_) => None
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
  if is_reserved_symbol(name) {
    return Err(ReservedSymbol)
  }
  match type_of(rhs) {
    Some(ty) =>
      match sig_add_const_idempotent_e(sig, name, ty) {
        Ok(sig2) =>
          match sig_mk_const_e(sig2, name) {
            Ok(c) =>
              match mk_eq(c, rhs) {
                Ok(eq) => Ok((sig2, eq))
                Err(_) => Err(InvalidConstRhs)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    None => Err(InvalidConstRhs)
  }
}

///|
pub fn empty_kernel_state() -> KernelState {
  KernelState::{
    sig: empty_sig(),
    theory: TheoryState::{ def_heads: [], witnessed_tycons: [] },
  }
}

///|
pub fn ks_sig(state : KernelState) -> GlobalSig {
  state.sig
}

///|
pub fn ks_push_scope(state : KernelState) -> KernelState {
  KernelState::{ sig: sig_push_scope(state.sig), theory: state.theory }
}

///|
pub fn ks_pop_scope(state : KernelState) -> Result[KernelState, SigError] {
  match sig_pop_scope(state.sig) {
    Some(sig2) => Ok(KernelState::{ sig: sig2, theory: state.theory })
    None => Err(ScopeUnderflow)
  }
}

///|
pub fn ks_lookup_const(state : KernelState, name : String) -> HolType? {
  sig_lookup_const(state.sig, name)
}

///|
pub fn ks_add_const(
  state : KernelState,
  name : String,
  ty : HolType,
) -> Result[KernelState, SigError] {
  match sig_add_const_idempotent_e(state.sig, name, ty) {
    Ok(sig2) => Ok(KernelState::{ sig: sig2, theory: state.theory })
    Err(e) => Err(e)
  }
}

///|
pub fn ks_has_def_head(state : KernelState, name : String) -> Bool {
  state.theory.def_heads.contains(name)
}

///|
pub fn ks_has_type_witness(
  state : KernelState,
  tycon : String,
  arity : Int,
) -> Bool {
  state.theory.witnessed_tycons.any(fn(pair) {
    let (name, a) = pair
    name == tycon && a == arity
  })
}

///|
pub fn ks_const_schema(state : KernelState, name : String) -> HolType? {
  sig_lookup_const(state.sig, name)
}

///|
pub fn ks_type_is_admissible(state : KernelState, ty : HolType) -> Bool {
  match ty {
    TyVal(_) => true
    TyApp(tycon, args) => {
      let tycon_ok = is_builtin_tycon(tycon, args.length()) ||
        ks_has_type_witness(state, tycon, args.length())
      tycon_ok && args.all(fn(arg) { ks_type_is_admissible(state, arg) })
    }
  }
}

///|
pub fn ks_type_subst_is_admissible(
  state : KernelState,
  subst : Array[(String, HolType)],
) -> Bool {
  subst.all(fn(kv) {
    let (_, ty) = kv
    ks_type_is_admissible(state, ty)
  })
}

///|
pub fn ks_register_type_definition(
  state : KernelState,
  tycon : String,
  arity : Int,
  witness_ok : Bool,
) -> Result[KernelState, SigError] {
  if !witness_ok {
    return Err(TypeDefWitnessMissing)
  }
  if is_builtin_tycon(tycon, arity) {
    return Ok(state)
  }
  if ks_has_type_witness(state, tycon, arity) {
    return Ok(state)
  }
  let witnessed = state.theory.witnessed_tycons.copy()
  witnessed.push((tycon, arity))
  Ok(KernelState::{
    sig: state.sig,
    theory: TheoryState::{
      def_heads: state.theory.def_heads,
      witnessed_tycons: witnessed,
    },
  })
}

///|
pub fn ks_define_const(
  state : KernelState,
  name : String,
  decl_ty : HolType,
  rhs : Term,
) -> Result[(KernelState, Term), SigError] {
  if is_reserved_symbol(name) {
    return Err(ReservedSymbol)
  }
  if ks_has_def_head(state, name) {
    return Err(DefinitionAlreadyExists)
  }
  if !term_is_closed(rhs) {
    return Err(DefinitionNotClosed)
  }
  if term_has_const_named(rhs, name) {
    return Err(DefinitionIsCyclic)
  }
  match type_of(rhs) {
    Some(rhs_ty) => {
      if !ty_eq(rhs_ty, decl_ty) {
        return Err(TypeMismatch)
      }
      if !term_tyvars_subset(rhs, decl_ty) {
        return Err(GhostTypeVariable)
      }
      match sig_add_const(state.sig, name, decl_ty) {
        Some(sig2) =>
          match sig_mk_const(sig2, name) {
            Some(c) =>
              match mk_eq(c, rhs) {
                Ok(def_eq) => {
                  let def_heads = state.theory.def_heads.copy()
                  def_heads.push(name)
                  let state2 = KernelState::{
                    sig: sig2,
                    theory: TheoryState::{
                      def_heads,
                      witnessed_tycons: state.theory.witnessed_tycons,
                    },
                  }
                  Ok((state2, def_eq))
                }
                Err(_) => Err(InvalidConstRhs)
              }
            None => Err(UnknownConst)
          }
        None => Err(DuplicateConstName)
      }
    }
    None => Err(InvalidConstRhs)
  }
}

///|
/// Trusted definition extension that also returns the generated definition theorem.
pub fn ks_define_const_thm(
  state : KernelState,
  name : String,
  decl_ty : HolType,
  rhs : Term,
) -> Result[(KernelState, Thm), SigError] {
  match ks_define_const(state, name, decl_ty, rhs) {
    Ok((state2, def_eq)) =>
      match to_db_term(def_eq) {
        Some(eq_db) => Ok((state2, mk_thm([], eq_db)))
        None => Err(InvalidConstRhs)
      }
    Err(e) => Err(e)
  }
}
