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
  InvalidTypeAbsName
  InvalidTypeParams
  InvalidTypeArity
  TypeWitnessArityMismatch
  TypeWitnessPredicateMismatch
  TypeConstructorAlreadyExists
  TypeRepresentationAlreadyExists
  TypeAbstractionAlreadyExists
  InvalidInfinityAnchor
  MissingInfinityAnchor
  InvalidTypeDefinitionProduct
  MissingTypeDefinitionContract
  InvalidSpecificationWitness
  InvalidSpecificationPredicate
  SpecificationTypeVarLeak
  TypeMismatch
}

///|
pub type ConstId = Int

///|
pub enum ExtensionGate {
  DefOK
  TypeDefOK
  SpecOK
}

///|
pub type ExtensionCert = (ExtensionGate, Array[String], String)

///|
priv struct TheoryState {
  def_heads : Array[String]
  def_const_deps : Array[(String, Array[String])]
  witnessed_tycons : Array[(String, Int)]
  type_rep_heads : Array[String]
  type_abs_heads : Array[String]
  typedef_contracts : Array[(String, Thm, Thm, Thm)]
  extension_certs : Array[ExtensionCert]
  ind_infinity_axiom : Thm?
  next_const_id : ConstId
}

///|
struct KernelState {
  sig : GlobalSig
  theory : TheoryState
}

///|
fn is_reserved_symbol(name : String) -> Bool {
  name == "=" || name == "@"
}

///|
fn is_builtin_tycon(name : String, arity : Int) -> Bool {
  (name == "bool" && arity == 0) ||
  (name == "fun" && arity == 2) ||
  (name == "ind" && arity == 0)
}

///|
fn choice_schema_ty() -> HolType {
  let a = mk_tyvar("A")
  fun_ty(fun_ty(a, bool_ty()), a)
}

///|
fn initial_sig() -> GlobalSig {
  Sig([[("@", 0, choice_schema_ty())]])
}

///|
fn append_extension_cert(
  state : KernelState,
  gate : ExtensionGate,
  heads : Array[String],
  witness_digest : String,
) -> KernelState {
  let certs = state.theory.extension_certs.copy()
  certs.push((gate, heads, witness_digest))
  KernelState::{
    sig: state.sig,
    theory: TheoryState::{
      def_heads: state.theory.def_heads,
      def_const_deps: state.theory.def_const_deps,
      witnessed_tycons: state.theory.witnessed_tycons,
      type_rep_heads: state.theory.type_rep_heads,
      type_abs_heads: state.theory.type_abs_heads,
      typedef_contracts: state.theory.typedef_contracts,
      extension_certs: certs,
      ind_infinity_axiom: state.theory.ind_infinity_axiom,
      next_const_id: state.theory.next_const_id,
    },
  }
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
    sig: initial_sig(),
    theory: TheoryState::{
      def_heads: [],
      def_const_deps: [],
      witnessed_tycons: [("ind", 0)],
      type_rep_heads: [],
      type_abs_heads: [],
      typedef_contracts: [],
      extension_certs: [],
      ind_infinity_axiom: None,
      next_const_id: 1,
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
  if ks_has_type_abs_head(state, name) {
    return Err(TypeAbstractionAlreadyExists)
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
              type_abs_heads: state.theory.type_abs_heads,
              typedef_contracts: state.theory.typedef_contracts,
              extension_certs: state.theory.extension_certs,
              ind_infinity_axiom: state.theory.ind_infinity_axiom,
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
pub fn ks_has_type_abs_head(state : KernelState, name : String) -> Bool {
  state.theory.type_abs_heads.contains(name)
}

///|
fn lookup_typedef_contract(
  contracts : Array[(String, Thm, Thm, Thm)],
  tycon : String,
) -> (Thm, Thm, Thm)? {
  for entry in contracts {
    let (name, abs_rep, rep_range, rep_abs) = entry
    if name == tycon {
      return Some((abs_rep, rep_range, rep_abs))
    }
  }
  None
}

///|
pub fn ks_has_typedef_contract(state : KernelState, tycon : String) -> Bool {
  lookup_typedef_contract(state.theory.typedef_contracts, tycon) is Some(_)
}

///|
pub fn ks_typedef_contract(
  state : KernelState,
  tycon : String,
) -> Result[(Thm, Thm, Thm), SigError] {
  match lookup_typedef_contract(state.theory.typedef_contracts, tycon) {
    Some(v) => Ok(v)
    None => Err(MissingTypeDefinitionContract)
  }
}

///|
pub fn ks_extension_cert_count(state : KernelState) -> Int {
  state.theory.extension_certs.length()
}

///|
pub fn ks_extension_cert_at(state : KernelState, idx : Int) -> ExtensionCert? {
  if idx < 0 || idx >= state.theory.extension_certs.length() {
    None
  } else {
    Some(state.theory.extension_certs[idx])
  }
}

///|
pub fn ks_has_ind_infinity_axiom(state : KernelState) -> Bool {
  state.theory.ind_infinity_axiom is Some(_)
}

///|
pub fn ks_ind_infinity_axiom(state : KernelState) -> Result[Thm, SigError] {
  match state.theory.ind_infinity_axiom {
    Some(th) => Ok(th)
    None => Err(MissingInfinityAnchor)
  }
}

///|
fn type_has_tycon(ty : HolType, tycon : String) -> Bool {
  match ty {
    TyVal(_) => false
    TyApp(name, args) =>
      if name == tycon {
        true
      } else {
        args.any(fn(arg) { type_has_tycon(arg, tycon) })
      }
  }
}

///|
fn term_mentions_tycon(term : Term, tycon : String) -> Bool {
  let node_type_mentions = match type_of(term) {
    Some(ty) => type_has_tycon(ty, tycon)
    None => false
  }
  if node_type_mentions {
    return true
  }
  match term {
    Var(_, ty) => type_has_tycon(ty, tycon)
    Const(_, ty) => type_has_tycon(ty, tycon)
    Comb(f, x) => term_mentions_tycon(f, tycon) || term_mentions_tycon(x, tycon)
    Abs(v, body) =>
      term_mentions_tycon(v, tycon) || term_mentions_tycon(body, tycon)
  }
}

///|
fn apply_unary_predicate(predicate : Term, arg : Term) -> Term? {
  match to_db_term(predicate) {
    Some(DbAbs(dom_ty, body_db)) =>
      match (type_of(arg), to_db_term(arg)) {
        (Some(arg_ty), Some(arg_db)) =>
          if !ty_eq(arg_ty, dom_ty) {
            None
          } else {
            match db_beta_reduce_once(DbComb(DbAbs(dom_ty, body_db), arg_db)) {
              Some(out_db) => from_db_term(out_db)
              None => None
            }
          }
        _ => None
      }
    _ => None
  }
}

///|
fn mk_thm_from_terms(
  state : KernelState,
  hyps : Array[Term],
  concl : Term,
) -> Result[Thm, SigError] {
  let hyps_db : Array[DbTerm] = []
  for h in hyps {
    match to_db_term(h) {
      Some(h_db) => hyps_db.push(h_db)
      None => return Err(InvalidTypeDefinitionProduct)
    }
  }
  match to_db_term(concl) {
    Some(c_db) =>
      match thm_bind_const_ids(state, mk_thm(hyps_db, c_db)) {
        Ok(th) => Ok(th)
        Err(_) => Err(InvalidTypeDefinitionProduct)
      }
    None => Err(InvalidTypeDefinitionProduct)
  }
}

///|
pub fn ks_register_ind_infinity_axiom(
  state : KernelState,
  anchor : Thm,
) -> Result[KernelState, SigError] {
  if state.theory.ind_infinity_axiom is Some(_) {
    return Err(InvalidInfinityAnchor)
  }
  if thm_hyp_count(anchor) != 0 {
    return Err(InvalidInfinityAnchor)
  }
  if !thm_is_admissible(state, anchor) {
    return Err(InvalidInfinityAnchor)
  }
  match thm_concl(anchor) {
    Ok(concl) =>
      match type_of(concl) {
        Some(ty) =>
          if !is_bool_ty(ty) || !term_mentions_tycon(concl, "ind") {
            Err(InvalidInfinityAnchor)
          } else {
            Ok(KernelState::{
              sig: state.sig,
              theory: TheoryState::{
                def_heads: state.theory.def_heads,
                def_const_deps: state.theory.def_const_deps,
                witnessed_tycons: state.theory.witnessed_tycons,
                type_rep_heads: state.theory.type_rep_heads,
                type_abs_heads: state.theory.type_abs_heads,
                typedef_contracts: state.theory.typedef_contracts,
                extension_certs: state.theory.extension_certs,
                ind_infinity_axiom: Some(anchor),
                next_const_id: state.theory.next_const_id,
              },
            })
          }
        None => Err(InvalidInfinityAnchor)
      }
    Err(_) => Err(InvalidInfinityAnchor)
  }
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
pub fn ks_term_in_language(state : KernelState, term : Term) -> Bool {
  term_const_instances_ok(state, term)
}

///|
pub fn ks_thm_is_sentence_in_language(state : KernelState, th : Thm) -> Bool {
  if thm_hyp_count(th) != 0 {
    return false
  }
  match thm_concl(th) {
    Ok(concl) =>
      match type_of(concl) {
        Some(ty) => is_bool_ty(ty) && term_const_instances_ok(state, concl)
        None => false
      }
    Err(_) => false
  }
}

///|
pub fn ks_conservative_replay_ok(
  base_state : KernelState,
  extended_state : KernelState,
  th : Thm,
) -> Bool {
  thm_is_admissible(extended_state, th) &&
  ks_thm_is_sentence_in_language(base_state, th) &&
  thm_is_admissible(base_state, th)
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
  let abs_name = "Abs_" + tycon
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
  if abs_name == "" || is_reserved_symbol(abs_name) || abs_name == rep_name {
    return Err(InvalidTypeAbsName)
  }
  if ks_has_tycon(state, tycon) {
    return Err(TypeConstructorAlreadyExists)
  }
  if ks_has_type_rep_head(state, rep_name) ||
    ks_has_type_abs_head(state, rep_name) ||
    ks_has_def_head(state, rep_name) {
    return Err(TypeRepresentationAlreadyExists)
  }
  if ks_lookup_const(state, rep_name) is Some(_) {
    return Err(TypeRepresentationAlreadyExists)
  }
  if ks_has_type_abs_head(state, abs_name) ||
    ks_has_type_rep_head(state, abs_name) ||
    ks_has_def_head(state, abs_name) {
    return Err(TypeAbstractionAlreadyExists)
  }
  if ks_lookup_const(state, abs_name) is Some(_) {
    return Err(TypeAbstractionAlreadyExists)
  }
  if !term_is_closed(predicate) {
    return Err(InvalidTypePredicate)
  }
  let (rep_ty, pred_body) = match predicate {
    Abs(v, body) =>
      match v {
        Var(_, dom_ty) =>
          match type_of(predicate) {
            Some(TyApp("fun", [pred_dom, pred_cod])) =>
              if !ty_eq(dom_ty, pred_dom) || !is_bool_ty(pred_cod) {
                return Err(InvalidTypePredicate)
              } else {
                (dom_ty, body)
              }
            _ => return Err(InvalidTypePredicate)
          }
        _ => return Err(InvalidTypePredicate)
      }
    _ => return Err(InvalidTypePredicate)
  }
  match type_of(pred_body) {
    Some(pred_body_ty) =>
      if !is_bool_ty(pred_body_ty) {
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
      if !term_alpha_eq(c, pred_body) {
        return Err(TypeWitnessPredicateMismatch)
      }
    Err(_) => return Err(InvalidTypeWitness)
  }
  let type_params = params.map(fn(p) { mk_tyvar(p) })
  let new_ty = mk_tyapp(tycon, type_params)
  let rep_ty_schema = fun_ty(new_ty, rep_ty)
  let abs_ty_schema = fun_ty(rep_ty, new_ty)
  let sig1 = match
    sig_add_const_with_id(
      state.sig,
      rep_name,
      rep_ty_schema,
      state.theory.next_const_id,
    ) {
    Ok(sig) => sig
    Err(DuplicateConstName) => return Err(TypeRepresentationAlreadyExists)
    Err(_) => return Err(TypeRepresentationAlreadyExists)
  }
  let sig2 = match
    sig_add_const_with_id(
      sig1,
      abs_name,
      abs_ty_schema,
      state.theory.next_const_id + 1,
    ) {
    Ok(sig) => sig
    Err(DuplicateConstName) => return Err(TypeAbstractionAlreadyExists)
    Err(_) => return Err(TypeAbstractionAlreadyExists)
  }
  let witnessed = state.theory.witnessed_tycons.copy()
  witnessed.push((tycon, arity))
  let reps = state.theory.type_rep_heads.copy()
  reps.push(rep_name)
  let abses = state.theory.type_abs_heads.copy()
  abses.push(abs_name)
  let state1 = KernelState::{
    sig: sig2,
    theory: TheoryState::{
      def_heads: state.theory.def_heads,
      def_const_deps: state.theory.def_const_deps,
      witnessed_tycons: witnessed,
      type_rep_heads: reps,
      type_abs_heads: abses,
      typedef_contracts: state.theory.typedef_contracts,
      extension_certs: state.theory.extension_certs,
      ind_infinity_axiom: state.theory.ind_infinity_axiom,
      next_const_id: state.theory.next_const_id + 2,
    },
  }

  let rep_const = mk_const(rep_name, rep_ty_schema)
  let abs_const = mk_const(abs_name, abs_ty_schema)
  let a = mk_var("a", new_ty)
  let r = mk_var("r", rep_ty)

  let abs_rep_eq = match mk_eq(mk_comb(abs_const, mk_comb(rep_const, a)), a) {
    Ok(eq) => eq
    Err(_) => return Err(InvalidTypeDefinitionProduct)
  }
  let rep_range = match
    apply_unary_predicate(predicate, mk_comb(rep_const, a)) {
    Some(term) => term
    None => return Err(InvalidTypeDefinitionProduct)
  }
  let rep_abs_eq = match mk_eq(mk_comb(rep_const, mk_comb(abs_const, r)), r) {
    Ok(eq) => eq
    Err(_) => return Err(InvalidTypeDefinitionProduct)
  }
  let rep_abs_hyp = match apply_unary_predicate(predicate, r) {
    Some(term) => term
    None => return Err(InvalidTypeDefinitionProduct)
  }

  let abs_rep_th = match mk_thm_from_terms(state1, [], abs_rep_eq) {
    Ok(th) => th
    Err(e) => return Err(e)
  }
  let rep_range_th = match mk_thm_from_terms(state1, [], rep_range) {
    Ok(th) => th
    Err(e) => return Err(e)
  }
  let rep_abs_th = match mk_thm_from_terms(state1, [rep_abs_hyp], rep_abs_eq) {
    Ok(th) => th
    Err(e) => return Err(e)
  }

  let contracts = state.theory.typedef_contracts.copy()
  contracts.push((tycon, abs_rep_th, rep_range_th, rep_abs_th))
  let state2 = KernelState::{
    sig: state1.sig,
    theory: TheoryState::{
      def_heads: state1.theory.def_heads,
      def_const_deps: state1.theory.def_const_deps,
      witnessed_tycons: state1.theory.witnessed_tycons,
      type_rep_heads: state1.theory.type_rep_heads,
      type_abs_heads: state1.theory.type_abs_heads,
      typedef_contracts: contracts,
      extension_certs: state1.theory.extension_certs,
      ind_infinity_axiom: state1.theory.ind_infinity_axiom,
      next_const_id: state1.theory.next_const_id,
    },
  }
  Ok(
    append_extension_cert(
      state2,
      TypeDefOK,
      [tycon, rep_name, abs_name],
      thm_to_string(witness),
    ),
  )
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
  if ks_has_type_abs_head(state, name) {
    return Err(TypeAbstractionAlreadyExists)
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
                      type_abs_heads: state.theory.type_abs_heads,
                      typedef_contracts: state.theory.typedef_contracts,
                      extension_certs: state.theory.extension_certs,
                      ind_infinity_axiom: state.theory.ind_infinity_axiom,
                      next_const_id: state.theory.next_const_id + 1,
                    },
                  }
                  let digest = match to_db_term(def_eq) {
                    Some(eq_db) =>
                      match
                        thm_bind_const_ids(state2, mk_def_thm(name, eq_db)) {
                        Ok(def_th) => thm_to_string(def_th)
                        Err(_) => return Err(InvalidConstRhs)
                      }
                    None => return Err(InvalidConstRhs)
                  }
                  let state3 = append_extension_cert(
                    state2,
                    DefOK,
                    [name],
                    digest,
                  )
                  Ok((state3, def_eq))
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

///|
/// Controlled specification admission over choice plus definitional extension.
/// Returns the updated state and the admitted theorem `|- P(c)`.
pub fn ks_specify_const(
  state : KernelState,
  name : String,
  decl_ty : HolType,
  predicate : Term,
  witness : Thm,
) -> Result[(KernelState, Thm), SigError] {
  if !term_is_closed(predicate) {
    return Err(InvalidSpecificationPredicate)
  }
  let (pred_dom, pred_body) = match predicate {
    Abs(v, body) =>
      match v {
        Var(_, dom_ty) =>
          match type_of(predicate) {
            Some(TyApp("fun", [dom2, cod])) =>
              if !ty_eq(dom_ty, dom2) || !is_bool_ty(cod) {
                return Err(InvalidSpecificationPredicate)
              } else {
                (dom_ty, body)
              }
            _ => return Err(InvalidSpecificationPredicate)
          }
        _ => return Err(InvalidSpecificationPredicate)
      }
    _ => return Err(InvalidSpecificationPredicate)
  }
  if !ty_eq(pred_dom, decl_ty) {
    return Err(InvalidSpecificationPredicate)
  }
  let decl_tyvars = tyvars(decl_ty)
  let pred_tyvars = term_tyvars(predicate)
  if !pred_tyvars.all(fn(tv) { decl_tyvars.contains(tv) }) {
    return Err(SpecificationTypeVarLeak)
  }
  if thm_hyp_count(witness) != 0 {
    return Err(InvalidSpecificationWitness)
  }
  if !thm_is_admissible(state, witness) {
    return Err(InvalidSpecificationWitness)
  }
  match thm_concl(witness) {
    Ok(c) =>
      if !term_alpha_eq(c, pred_body) {
        return Err(InvalidSpecificationWitness)
      }
    Err(_) => return Err(InvalidSpecificationWitness)
  }
  let rhs = mk_comb(
    mk_const("@", fun_ty(fun_ty(decl_ty, bool_ty()), decl_ty)),
    predicate,
  )
  match ks_define_const_thm(state, name, decl_ty, rhs) {
    Ok((state2, _def_th)) =>
      match ks_mk_const(state2, name) {
        Ok(c) =>
          match apply_unary_predicate(predicate, c) {
            Some(pc_term) =>
              match mk_thm_from_terms(state2, [], pc_term) {
                Ok(pc_th) =>
                  Ok(
                    (
                      append_extension_cert(
                        state2,
                        SpecOK,
                        [name],
                        thm_to_string(witness),
                      ),
                      pc_th,
                    ),
                  )
                Err(_) => Err(InvalidSpecificationWitness)
              }
            None => Err(InvalidSpecificationPredicate)
          }
        Err(_) => Err(InvalidSpecificationPredicate)
      }
    Err(e) => Err(e)
  }
}
