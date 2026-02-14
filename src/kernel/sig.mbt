///|
/// Scoped constant signature used for name lookup.
pub enum GlobalSig {
  Sig(Array[Array[(String, ConstId, HolType)]])
}

///|
/// Signature and admissibility errors.
pub suberror SigError {
  DuplicateConstName
  ConstTypeConflict
  InvalidConstInstance
  UnknownConst
  ScopeUnderflow
  InvalidConstRhs
  ReservedSymbol
  DefinitionAlreadyExists
  DefinitionNotClosed
  DefinitionIsCyclic
  GhostTypeVariable
  InvalidTypeWitness
  InvalidTypePredicate
  InvalidTypeRepName
  InvalidTypeParams
  InvalidTypeArity
  TypeWitnessArityMismatch
  TypeWitnessPredicateMismatch
  TypeConstructorAlreadyExists
  TypeRepresentationAlreadyExists
  TypeMismatch
}

///|
pub type ConstId = Int

///|
priv struct TheoryState {
  def_heads : Array[String]
  def_const_deps : Array[(String, Array[String])]
  witnessed_tycons : Array[(String, Int)]
  type_rep_heads : Array[String]
  next_const_id : ConstId
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
fn sig_pop_scope(sig : GlobalSig) -> GlobalSig? {
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
fn lookup_in_scope(
  scope : Array[(String, ConstId, HolType)],
  name : String,
) -> (ConstId, HolType)? {
  for entry in scope {
    let (n, id, ty) = entry
    if n == name {
      return Some((id, ty))
    }
  }
  None
}

///|
fn current_scope_lookup(sig : GlobalSig, name : String) -> (ConstId, HolType)? {
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
  match sig_lookup_const_with_id(sig, name) {
    Some((_, ty)) => Some(ty)
    None => None
  }
}

///|
pub fn sig_lookup_const_id(sig : GlobalSig, name : String) -> ConstId? {
  match sig_lookup_const_with_id(sig, name) {
    Some((id, _)) => Some(id)
    None => None
  }
}

///|
fn sig_lookup_const_with_id(
  sig : GlobalSig,
  name : String,
) -> (ConstId, HolType)? {
  match sig {
    Sig(scopes) => {
      let mut i = scopes.length()
      while i > 0 {
        i = i - 1
        match lookup_in_scope(scopes[i], name) {
          Some((id, ty)) => return Some((id, ty))
          None => ()
        }
      }
      None
    }
  }
}

///|
fn sig_next_const_id(sig : GlobalSig) -> ConstId {
  let mut next = 0
  match sig {
    Sig(scopes) =>
      for scope in scopes {
        for entry in scope {
          let (_, id, _) = entry
          if id >= next {
            next = id + 1
          }
        }
      }
  }
  next
}

///|
fn sig_add_const(sig : GlobalSig, name : String, ty : HolType) -> GlobalSig? {
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
            let id = sig_next_const_id(sig)
            let out = scopes.copy()
            let top = out[out.length() - 1].copy()
            top.push((name, id, ty))
            out[out.length() - 1] = top
            Some(Sig(out))
          }
      }
  }
}

///|
fn sig_add_const_with_id(
  sig : GlobalSig,
  name : String,
  ty : HolType,
  id : ConstId,
) -> Result[GlobalSig, SigError] {
  if is_reserved_symbol(name) {
    return Err(ReservedSymbol)
  }
  match current_scope_lookup(sig, name) {
    Some(_) => Err(DuplicateConstName)
    None =>
      match sig {
        Sig(scopes) =>
          if scopes.length() == 0 {
            Err(ScopeUnderflow)
          } else {
            let out = scopes.copy()
            let top = out[out.length() - 1].copy()
            top.push((name, id, ty))
            out[out.length() - 1] = top
            Ok(Sig(out))
          }
      }
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
    Some((_, existing)) =>
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
fn sig_mk_const(sig : GlobalSig, name : String) -> Term? {
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
pub fn sig_mk_const_instance_e(
  sig : GlobalSig,
  name : String,
  inst_ty : HolType,
) -> Result[Term, SigError] {
  match sig_lookup_const(sig, name) {
    Some(schema) =>
      if ty_is_instance_of(inst_ty, schema) {
        Ok(mk_const(name, inst_ty))
      } else {
        Err(InvalidConstInstance)
      }
    None => Err(UnknownConst)
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
    theory: TheoryState::{
      def_heads: [],
      def_const_deps: [],
      witnessed_tycons: [],
      type_rep_heads: [],
      next_const_id: 0,
    },
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
pub fn ks_mk_const(
  state : KernelState,
  name : String,
) -> Result[Term, SigError] {
  sig_mk_const_e(state.sig, name)
}

///|
pub fn ks_mk_const_instance(
  state : KernelState,
  name : String,
  inst_ty : HolType,
) -> Result[Term, SigError] {
  sig_mk_const_instance_e(state.sig, name, inst_ty)
}

///|
pub fn ks_add_const(
  state : KernelState,
  name : String,
  ty : HolType,
) -> Result[KernelState, SigError] {
  if is_reserved_symbol(name) {
    return Err(ReservedSymbol)
  }
  if ks_has_def_head(state, name) {
    return Err(DefinitionAlreadyExists)
  }
  if ks_has_type_rep_head(state, name) {
    return Err(TypeRepresentationAlreadyExists)
  }
  match current_scope_lookup(state.sig, name) {
    Some((_, existing)) =>
      if ty_eq(existing, ty) {
        Ok(state)
      } else {
        Err(ConstTypeConflict)
      }
    None =>
      match
        sig_add_const_with_id(state.sig, name, ty, state.theory.next_const_id) {
        Ok(sig2) =>
          Ok(KernelState::{
            sig: sig2,
            theory: TheoryState::{
              def_heads: state.theory.def_heads,
              def_const_deps: state.theory.def_const_deps,
              witnessed_tycons: state.theory.witnessed_tycons,
              type_rep_heads: state.theory.type_rep_heads,
              next_const_id: state.theory.next_const_id + 1,
            },
          })
        Err(e) => Err(e)
      }
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
pub fn ks_has_type_rep_head(state : KernelState, name : String) -> Bool {
  state.theory.type_rep_heads.contains(name)
}

///|
fn ks_has_tycon(state : KernelState, tycon : String) -> Bool {
  if tycon == "bool" || tycon == "fun" {
    return true
  }
  state.theory.witnessed_tycons.any(fn(pair) {
    let (name, _) = pair
    name == tycon
  })
}

///|
pub fn ks_const_schema(state : KernelState, name : String) -> HolType? {
  sig_lookup_const(state.sig, name)
}

///|
fn eq_const_type_ok(ty : HolType) -> Bool {
  match ty {
    TyApp("fun", [lhs, TyApp("fun", [rhs, TyApp("bool", [])])]) =>
      ty_eq(lhs, rhs)
    _ => false
  }
}

///|
fn term_const_instances_ok(state : KernelState, term : Term) -> Bool {
  match term {
    Var(_, _) => true
    Const(name, inst_ty) =>
      if name == "=" {
        eq_const_type_ok(inst_ty)
      } else {
        match ks_const_schema(state, name) {
          Some(schema_ty) => ty_is_instance_of(inst_ty, schema_ty)
          None => false
        }
      }
    Comb(f, x) =>
      term_const_instances_ok(state, f) && term_const_instances_ok(state, x)
    Abs(_, body) => term_const_instances_ok(state, body)
  }
}

///|
fn push_unique_name(out : Array[String], name : String) -> Unit {
  if !out.contains(name) {
    out.push(name)
  }
}

///|
fn collect_term_const_names(term : Term, out : Array[String]) -> Unit {
  match term {
    Var(_, _) => ()
    Const(name, _) => if name != "=" { push_unique_name(out, name) }
    Comb(f, x) => {
      collect_term_const_names(f, out)
      collect_term_const_names(x, out)
    }
    Abs(_, body) => collect_term_const_names(body, out)
  }
}

///|
fn term_const_names(term : Term) -> Array[String] {
  let out : Array[String] = []
  collect_term_const_names(term, out)
  out
}

///|
fn lookup_def_deps(
  deps : Array[(String, Array[String])],
  name : String,
) -> Array[String]? {
  for entry in deps {
    let (head, rhs) = entry
    if head == name {
      return Some(rhs)
    }
  }
  None
}

///|
fn def_dep_path_exists(
  deps : Array[(String, Array[String])],
  start : String,
  target : String,
  visited : Array[String],
) -> Bool {
  if start == target {
    return true
  }
  if visited.contains(start) {
    return false
  }
  visited.push(start)
  match lookup_def_deps(deps, start) {
    Some(nexts) => {
      for next in nexts {
        if def_dep_path_exists(deps, next, target, visited) {
          return true
        }
      }
      false
    }
    None => false
  }
}

///|
fn def_cycle_would_form(
  deps : Array[(String, Array[String])],
  new_head : String,
  new_rhs_consts : Array[String],
) -> Bool {
  for name in new_rhs_consts {
    let visited : Array[String] = []
    if def_dep_path_exists(deps, name, new_head, visited) {
      return true
    }
  }
  false
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
pub fn ks_lookup_const_id(state : KernelState, name : String) -> ConstId? {
  sig_lookup_const_id(state.sig, name)
}

///|
pub fn ks_register_type_definition(
  state : KernelState,
  tycon : String,
  params : Array[String],
  rep_name : String,
  predicate : Term,
  witness : Thm,
) -> Result[KernelState, SigError] {
  if params.any(fn(p) { p == "" }) {
    return Err(InvalidTypeParams)
  }
  let mut i = 0
  while i < params.length() {
    let mut j = i + 1
    while j < params.length() {
      if params[i] == params[j] {
        return Err(InvalidTypeParams)
      }
      j = j + 1
    }
    i = i + 1
  }
  let arity = params.length()
  if arity < 0 {
    return Err(InvalidTypeArity)
  }
  if tycon == "" {
    return Err(InvalidTypeArity)
  }
  if rep_name == "" || is_reserved_symbol(rep_name) {
    return Err(InvalidTypeRepName)
  }
  if ks_has_tycon(state, tycon) {
    return Err(TypeConstructorAlreadyExists)
  }
  if ks_has_type_rep_head(state, rep_name) || ks_has_def_head(state, rep_name) {
    return Err(TypeRepresentationAlreadyExists)
  }
  if ks_lookup_const(state, rep_name) is Some(_) {
    return Err(TypeRepresentationAlreadyExists)
  }
  if !term_is_closed(predicate) {
    return Err(InvalidTypePredicate)
  }
  match type_of(predicate) {
    Some(pred_ty) =>
      if !is_bool_ty(pred_ty) {
        return Err(InvalidTypePredicate)
      }
    None => return Err(InvalidTypePredicate)
  }
  if !term_const_instances_ok(state, predicate) {
    return Err(InvalidTypePredicate)
  }
  let pred_tyvars = term_tyvars(predicate)
  if !pred_tyvars.all(fn(tv) { params.contains(tv) }) {
    return Err(TypeWitnessArityMismatch)
  }
  if thm_hyp_count(witness) != 0 {
    return Err(InvalidTypeWitness)
  }
  if !thm_is_admissible(state, witness) {
    return Err(InvalidTypeWitness)
  }
  match thm_concl(witness) {
    Ok(c) =>
      if !term_alpha_eq(c, predicate) {
        return Err(TypeWitnessPredicateMismatch)
      }
    Err(_) => return Err(InvalidTypeWitness)
  }
  let witnessed = state.theory.witnessed_tycons.copy()
  witnessed.push((tycon, arity))
  let reps = state.theory.type_rep_heads.copy()
  reps.push(rep_name)
  Ok(KernelState::{
    sig: state.sig,
    theory: TheoryState::{
      def_heads: state.theory.def_heads,
      def_const_deps: state.theory.def_const_deps,
      witnessed_tycons: witnessed,
      type_rep_heads: reps,
      next_const_id: state.theory.next_const_id,
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
  if ks_has_type_rep_head(state, name) {
    return Err(TypeRepresentationAlreadyExists)
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
      if !term_const_instances_ok(state, rhs) {
        return Err(InvalidConstRhs)
      }
      let rhs_consts = term_const_names(rhs)
      if def_cycle_would_form(state.theory.def_const_deps, name, rhs_consts) {
        return Err(DefinitionIsCyclic)
      }
      match
        sig_add_const_with_id(
          state.sig,
          name,
          decl_ty,
          state.theory.next_const_id,
        ) {
        Ok(sig2) =>
          match sig_mk_const(sig2, name) {
            Some(c) =>
              match mk_eq(c, rhs) {
                Ok(def_eq) => {
                  let def_heads = state.theory.def_heads.copy()
                  def_heads.push(name)
                  let def_const_deps = state.theory.def_const_deps.copy()
                  def_const_deps.push((name, rhs_consts))
                  let state2 = KernelState::{
                    sig: sig2,
                    theory: TheoryState::{
                      def_heads,
                      def_const_deps,
                      witnessed_tycons: state.theory.witnessed_tycons,
                      type_rep_heads: state.theory.type_rep_heads,
                      next_const_id: state.theory.next_const_id + 1,
                    },
                  }
                  Ok((state2, def_eq))
                }
                Err(_) => Err(InvalidConstRhs)
              }
            None => Err(UnknownConst)
          }
        Err(e) => Err(e)
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
        Some(eq_db) =>
          match thm_bind_const_ids(state2, mk_def_thm(name, eq_db)) {
            Ok(th) => Ok((state2, th))
            Err(_) => Err(InvalidConstRhs)
          }
        None => Err(InvalidConstRhs)
      }
    Err(e) => Err(e)
  }
}
