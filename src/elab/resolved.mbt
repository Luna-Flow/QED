///|
pub struct ElabCtx {
  locals : Array[(String, HolType)]
}

///|
pub struct ResolvedConst {
  name : String
  const_id : ConstId
  inst_ty : HolType
  schema_ty : HolType
}

///|
pub enum RTerm {
  RVar(String, HolType)
  RConst(ResolvedConst)
  RComb(RTerm, RTerm)
  RAbs(String, HolType, RTerm)
}

///|
pub enum ElabError {
  UnknownName(String)
  UnknownConst(String)
  InvalidConstInstance(String)
  ScopeResolutionMismatch
  CoreTypingFailure
}

///|
pub fn empty_elab_ctx() -> ElabCtx {
  ElabCtx::{ locals: [] }
}

///|
pub fn elab_ctx_from_locals(locals : Array[(String, HolType)]) -> ElabCtx {
  ElabCtx::{ locals, }
}

///|
pub fn elab_ctx_extend(ctx : ElabCtx, name : String, ty : HolType) -> ElabCtx {
  let locals = ctx.locals.copy()
  locals.push((name, ty))
  ElabCtx::{ locals, }
}

///|
fn elab_ctx_lookup(ctx : ElabCtx, name : String) -> HolType? {
  let mut i = ctx.locals.length()
  while i > 0 {
    i = i - 1
    let (n, ty) = ctx.locals[i]
    if n == name {
      return Some(ty)
    }
  }
  None
}

///|
pub fn elab_err_unknown_const(err : ElabError) -> Bool {
  match err {
    UnknownConst(_) => true
    _ => false
  }
}

///|
pub fn elab_err_unknown_name(err : ElabError) -> Bool {
  match err {
    UnknownName(_) => true
    _ => false
  }
}

///|
pub fn elab_err_invalid_const_instance(err : ElabError) -> Bool {
  match err {
    InvalidConstInstance(_) => true
    _ => false
  }
}

///|
pub fn elab_err_scope_resolution_mismatch(err : ElabError) -> Bool {
  match err {
    ScopeResolutionMismatch => true
    _ => false
  }
}

///|
pub fn elab_err_core_typing_failure(err : ElabError) -> Bool {
  match err {
    CoreTypingFailure => true
    _ => false
  }
}

///|
pub fn rconst_name(rc : ResolvedConst) -> String {
  rc.name
}

///|
pub fn rconst_id(rc : ResolvedConst) -> ConstId {
  rc.const_id
}

///|
pub fn rconst_inst_ty(rc : ResolvedConst) -> HolType {
  rc.inst_ty
}

///|
pub fn rconst_schema_ty(rc : ResolvedConst) -> HolType {
  rc.schema_ty
}

///|
pub fn rterm_eq(lhs : RTerm, rhs : RTerm) -> Bool {
  match (lhs, rhs) {
    (RVar(n1, ty1), RVar(n2, ty2)) => n1 == n2 && ty_eq(ty1, ty2)
    (RConst(c1), RConst(c2)) =>
      c1.name == c2.name &&
      c1.const_id == c2.const_id &&
      ty_eq(c1.inst_ty, c2.inst_ty) &&
      ty_eq(c1.schema_ty, c2.schema_ty)
    (RComb(f1, x1), RComb(f2, x2)) => rterm_eq(f1, f2) && rterm_eq(x1, x2)
    (RAbs(n1, ty1, b1), RAbs(n2, ty2, b2)) =>
      n1 == n2 && ty_eq(ty1, ty2) && rterm_eq(b1, b2)
    _ => false
  }
}

///|
pub fn rterm_var(name : String, ty : HolType) -> RTerm {
  RVar(name, ty)
}

///|
pub fn rterm_const(rc : ResolvedConst) -> RTerm {
  RConst(rc)
}

///|
pub fn rterm_comb(f : RTerm, x : RTerm) -> RTerm {
  RComb(f, x)
}

///|
pub fn rterm_abs(name : String, ty : HolType, body : RTerm) -> RTerm {
  RAbs(name, ty, body)
}

///|
pub fn rterm_collect_free_vars(term : RTerm) -> Array[(String, HolType)] {
  let out : Array[(String, HolType)] = []
  let bound : Array[(String, HolType)] = []
  rterm_collect_free_vars_with_bound(term, bound, out)
  out
}

///|
fn rterm_collect_free_vars_with_bound(
  term : RTerm,
  bound : Array[(String, HolType)],
  out : Array[(String, HolType)],
) -> Unit {
  match term {
    RVar(name, ty) => {
      let mut found = false
      let mut i = bound.length()
      while i > 0 {
        i = i - 1
        let (bn, bty) = bound[i]
        if bn == name && ty_eq(bty, ty) {
          found = true
          break
        }
      }
      if !found {
        out.push((name, ty))
      }
    }
    RConst(_) => ()
    RComb(f, x) => {
      rterm_collect_free_vars_with_bound(f, bound, out)
      rterm_collect_free_vars_with_bound(x, bound, out)
    }
    RAbs(name, ty, body) => {
      let bound2 = bound.copy()
      bound2.push((name, ty))
      rterm_collect_free_vars_with_bound(body, bound2, out)
    }
  }
}

///|
pub fn rterm_collect_consts(term : RTerm) -> Array[ResolvedConst] {
  let out : Array[ResolvedConst] = []
  rterm_collect_consts_go(term, out)
  out
}

///|
fn rterm_collect_consts_go(term : RTerm, out : Array[ResolvedConst]) -> Unit {
  match term {
    RVar(_, _) => ()
    RConst(rc) => out.push(rc)
    RComb(f, x) => {
      rterm_collect_consts_go(f, out)
      rterm_collect_consts_go(x, out)
    }
    RAbs(_, _, body) => rterm_collect_consts_go(body, out)
  }
}

///|
pub fn rterm_well_formed(
  state : KernelState,
  ctx : ElabCtx,
  term : RTerm,
) -> Bool {
  match elab_core_type_of(state, ctx, term) {
    Some(_) => true
    None => false
  }
}

///|
pub fn rterm_to_string(term : RTerm) -> String {
  match term {
    RVar(name, ty) => "RVar(" + name + " : " + hol_type_to_string(ty) + ")"
    RConst(rc) =>
      "RConst(" +
      rc.name +
      "#" +
      rc.const_id.to_string() +
      " : " +
      hol_type_to_string(rc.inst_ty) +
      " <= " +
      hol_type_to_string(rc.schema_ty) +
      ")"
    RComb(f, x) =>
      "RComb(" + rterm_to_string(f) + ", " + rterm_to_string(x) + ")"
    RAbs(name, ty, body) =>
      "RAbs(" +
      name +
      " : " +
      hol_type_to_string(ty) +
      ", " +
      rterm_to_string(body) +
      ")"
  }
}

///|
fn mk_resolved_const(
  name : String,
  const_id : ConstId,
  inst_ty : HolType,
  schema_ty : HolType,
) -> ResolvedConst {
  ResolvedConst::{ name, const_id, inst_ty, schema_ty }
}

///|
fn builtin_eq_schema(inst_ty : HolType) -> HolType {
  fun_ty(inst_ty, fun_ty(inst_ty, bool_ty()))
}

///|
fn builtin_eq_principal_schema() -> HolType {
  builtin_eq_schema(mk_tyvar("A"))
}

///|
pub fn elab_resolve_const(
  state : KernelState,
  name : String,
  inst_ty : HolType,
) -> Result[ResolvedConst, ElabError] {
  if name == "=" {
    return Ok(
      mk_resolved_const("=", -1, inst_ty, builtin_eq_principal_schema()),
    )
  }
  match (ks_lookup_const_id(state, name), ks_const_schema(state, name)) {
    (Some(id), Some(schema_ty)) =>
      if ty_is_instance_of(inst_ty, schema_ty) {
        Ok(mk_resolved_const(name, id, inst_ty, schema_ty))
      } else {
        Err(InvalidConstInstance(name))
      }
    (None, None) => Err(UnknownConst(name))
    _ => Err(ScopeResolutionMismatch)
  }
}

///|
pub fn elab_resolve_const_by_name(
  state : KernelState,
  name : String,
) -> Result[ResolvedConst, ElabError] {
  if name == "=" {
    let schema_ty = builtin_eq_principal_schema()
    return Ok(mk_resolved_const("=", -1, schema_ty, schema_ty))
  }
  match ks_const_schema(state, name) {
    Some(schema_ty) => elab_resolve_const(state, name, schema_ty)
    None => Err(UnknownConst(name))
  }
}

///|
pub fn elab_resolve_const_instance(
  state : KernelState,
  name : String,
  inst_ty : HolType,
) -> Result[RTerm, ElabError] {
  match elab_resolve_const(state, name, inst_ty) {
    Ok(rc) => Ok(RConst(rc))
    Err(e) => Err(e)
  }
}

///|
pub fn elab_resolve_var(name : String, ty : HolType) -> RTerm {
  RVar(name, ty)
}

///|
pub fn elab_resolve_name(
  state : KernelState,
  ctx : ElabCtx,
  name : String,
) -> Result[RTerm, ElabError] {
  match elab_ctx_lookup(ctx, name) {
    Some(ty) => Ok(RVar(name, ty))
    None =>
      match elab_resolve_const_by_name(state, name) {
        Ok(rc) => Ok(RConst(rc))
        Err(UnknownConst(_)) => Err(UnknownName(name))
        Err(e) => Err(e)
      }
  }
}

///|
pub fn elab_resolve_app(
  state : KernelState,
  ctx : ElabCtx,
  f : RTerm,
  x : RTerm,
) -> Result[RTerm, ElabError] {
  let out = RComb(f, x)
  match elab_core_type_of(state, ctx, out) {
    Some(_) => Ok(out)
    None => Err(CoreTypingFailure)
  }
}

///|
pub fn elab_resolve_abs(
  state : KernelState,
  ctx : ElabCtx,
  name : String,
  ty : HolType,
  body : RTerm,
) -> Result[RTerm, ElabError] {
  let out = RAbs(name, ty, body)
  match elab_core_type_of(state, ctx, out) {
    Some(_) => Ok(out)
    None => Err(CoreTypingFailure)
  }
}

///|
pub fn elab_resolve_eq(
  state : KernelState,
  ctx : ElabCtx,
  lhs : RTerm,
  rhs : RTerm,
) -> Result[RTerm, ElabError] {
  match
    (elab_core_type_of(state, ctx, lhs), elab_core_type_of(state, ctx, rhs)) {
    (Some(lhs_ty), Some(rhs_ty)) =>
      if ty_eq(lhs_ty, rhs_ty) {
        match
          elab_resolve_const(
            state,
            "=",
            fun_ty(lhs_ty, fun_ty(lhs_ty, bool_ty())),
          ) {
          Ok(eq_c) => {
            let out = RComb(RComb(RConst(eq_c), lhs), rhs)
            match elab_core_type_of(state, ctx, out) {
              Some(_) => Ok(out)
              None => Err(CoreTypingFailure)
            }
          }
          Err(e) => Err(e)
        }
      } else {
        Err(CoreTypingFailure)
      }
    _ => Err(CoreTypingFailure)
  }
}

///|
pub fn elab_core_type_of(
  state : KernelState,
  ctx : ElabCtx,
  term : RTerm,
) -> HolType? {
  match term {
    RVar(name, ty) =>
      match elab_ctx_lookup(ctx, name) {
        Some(bound_ty) => if ty_eq(bound_ty, ty) { Some(ty) } else { None }
        None => None
      }
    RConst(rc) =>
      if rc.name == "=" {
        let eq_schema = builtin_eq_principal_schema()
        if rc.const_id == -1 &&
          ty_eq(rc.schema_ty, eq_schema) &&
          ty_is_instance_of(rc.inst_ty, eq_schema) {
          Some(rc.inst_ty)
        } else {
          None
        }
      } else {
        match
          (ks_lookup_const_id(state, rc.name), ks_const_schema(state, rc.name)) {
          (Some(id), Some(schema_ty)) =>
            if id == rc.const_id &&
              ty_eq(rc.schema_ty, schema_ty) &&
              ty_is_instance_of(rc.inst_ty, schema_ty) {
              Some(rc.inst_ty)
            } else {
              None
            }
          _ => None
        }
      }
    RComb(f, x) =>
      match
        (elab_core_type_of(state, ctx, f), elab_core_type_of(state, ctx, x)) {
        (Some(f_ty), Some(x_ty)) =>
          match dest_fun_ty(f_ty) {
            Some((dom, cod)) => if ty_eq(dom, x_ty) { Some(cod) } else { None }
            None => None
          }
        _ => None
      }
    RAbs(name, ty, body) =>
      match elab_core_type_of(state, elab_ctx_extend(ctx, name, ty), body) {
        Some(body_ty) => Some(fun_ty(ty, body_ty))
        None => None
      }
  }
}

///|
pub fn elab_check_core_type(
  state : KernelState,
  ctx : ElabCtx,
  term : RTerm,
  ty : HolType,
) -> Bool {
  match elab_core_type_of(state, ctx, term) {
    Some(actual) => ty_eq(actual, ty)
    None => false
  }
}

///|
fn lower_to_term_go(term : RTerm) -> Term {
  match term {
    RVar(name, ty) => mk_var(name, ty)
    RConst(rc) =>
      if rc.name == "=" {
        mk_const(rc.name, rc.inst_ty)
      } else {
        mk_const_bound(rc.name, rc.inst_ty, rc.const_id)
      }
    RComb(f, x) => mk_comb(lower_to_term_go(f), lower_to_term_go(x))
    RAbs(name, ty, body) => mk_abs(mk_var(name, ty), lower_to_term_go(body))
  }
}

///|
pub fn elab_lower_to_term(term : RTerm) -> Result[Term, ElabError] {
  let out = lower_to_term_go(term)
  match type_of(out) {
    Some(_) => Ok(out)
    None => Err(CoreTypingFailure)
  }
}

///|
pub fn elab_lower_to_db(term : RTerm) -> Result[DbTerm, ElabError] {
  match elab_lower_to_term(term) {
    Ok(named) =>
      match to_db_term(named) {
        Some(db) => Ok(db)
        None => Err(CoreTypingFailure)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn elab_resolve_named_term(
  state : KernelState,
  ctx : ElabCtx,
  term : Term,
) -> Result[RTerm, ElabError] {
  match dest_var(term) {
    Some((name, ty)) =>
      match elab_ctx_lookup(ctx, name) {
        Some(bound_ty) =>
          if ty_eq(bound_ty, ty) {
            Ok(RVar(name, ty))
          } else {
            Err(CoreTypingFailure)
          }
        None => Err(UnknownName(name))
      }
    None =>
      match dest_const(term) {
        Some((name, inst_ty)) =>
          match elab_resolve_const(state, name, inst_ty) {
            Ok(rc) => Ok(RConst(rc))
            Err(UnknownConst(_)) => Err(UnknownConst(name))
            Err(e) => Err(e)
          }
        None =>
          match dest_comb(term) {
            Some((f, x)) =>
              match
                (
                  elab_resolve_named_term(state, ctx, f),
                  elab_resolve_named_term(state, ctx, x),
                ) {
                (Ok(rf), Ok(rx)) => elab_resolve_app(state, ctx, rf, rx)
                (Err(e), _) => Err(e)
                (_, Err(e)) => Err(e)
              }
            None =>
              match dest_abs(term) {
                Some((v, body)) =>
                  match dest_var(v) {
                    Some((name, ty)) =>
                      match
                        elab_resolve_named_term(
                          state,
                          elab_ctx_extend(ctx, name, ty),
                          body,
                        ) {
                        Ok(rb) => elab_resolve_abs(state, ctx, name, ty, rb)
                        Err(e) => Err(e)
                      }
                    None => Err(CoreTypingFailure)
                  }
                None =>
                  match dest_eq(term) {
                    Ok((lhs, rhs)) =>
                      match
                        (
                          elab_resolve_named_term(state, ctx, lhs),
                          elab_resolve_named_term(state, ctx, rhs),
                        ) {
                        (Ok(rl), Ok(rr)) => elab_resolve_eq(state, ctx, rl, rr)
                        (Err(e), _) => Err(e)
                        (_, Err(e)) => Err(e)
                      }
                    Err(_) => Err(CoreTypingFailure)
                  }
              }
          }
      }
  }
}

///|
pub fn elab_roundtrip_term(
  state : KernelState,
  ctx : ElabCtx,
  term : Term,
) -> Result[RTerm, ElabError] {
  match elab_resolve_named_term(state, ctx, term) {
    Ok(rt) =>
      match elab_lower_to_term(rt) {
        Ok(term2) =>
          if term_alpha_eq(term, term2) {
            Ok(rt)
          } else {
            Err(ScopeResolutionMismatch)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}
