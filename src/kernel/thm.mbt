///|
/// Kernel-visible error taxonomy aligned with the formal specification.
pub suberror LogicError {
  TypeMismatch
  VariableCaptured
  NotAnEquality
  NotBoolTerm
  AlphaMismatch
  InvalidInstantiation
  VarFreeInHyp
  NotTrivialBetaRedex
  BoundaryFailure
}

///|
/// Opaque theorem object.
struct Thm {
  hyps : Array[DbTerm]
  concl : DbTerm
  def_origin : String?
  const_ids : Array[(String, ConstId)]
}

///|
fn mk_thm_with_origin(
  hyps : Array[DbTerm],
  concl : DbTerm,
  def_origin : String?,
) -> Thm {
  Thm::{ hyps: db_hyps_dedup(hyps), concl, def_origin, const_ids: [] }
}

///|
fn mk_thm(hyps : Array[DbTerm], concl : DbTerm) -> Thm {
  mk_thm_with_origin(hyps, concl, None)
}

///|
fn mk_def_thm(def_head : String, concl : DbTerm) -> Thm {
  mk_thm_with_origin([], concl, Some(def_head))
}

///|
fn thm_with_const_ids(th : Thm, const_ids : Array[(String, ConstId)]) -> Thm {
  Thm::{ hyps: th.hyps, concl: th.concl, def_origin: th.def_origin, const_ids }
}

///|
fn lower_term(term : Term) -> Result[DbTerm, LogicError] {
  match to_db_term(term) {
    Some(t) => Ok(t)
    None => Err(BoundaryFailure)
  }
}

///|
fn lift_term(term : DbTerm) -> Result[Term, LogicError] {
  match from_db_term(term) {
    Some(t) => Ok(t)
    None => Err(BoundaryFailure)
  }
}

///|
fn db_dest_eq(term : DbTerm) -> Result[(DbTerm, DbTerm), LogicError] {
  match term {
    DbComb(DbComb(DbConst("=", eq_ty), lhs), rhs) =>
      match (db_type_of(lhs), db_type_of(rhs)) {
        (Some(lhs_ty), Some(rhs_ty)) =>
          if !db_eq_const_type_ok(eq_ty) {
            Err(TypeMismatch)
          } else {
            match dest_fun_ty(eq_ty) {
              Some((dom, cod)) =>
                match dest_fun_ty(cod) {
                  Some((rhs_dom, out)) =>
                    if ty_eq(dom, lhs_ty) &&
                      ty_eq(rhs_dom, rhs_ty) &&
                      ty_eq(dom, rhs_dom) &&
                      is_bool_ty(out) {
                      Ok((lhs, rhs))
                    } else {
                      Err(TypeMismatch)
                    }
                  None => Err(TypeMismatch)
                }
              None => Err(TypeMismatch)
            }
          }
        _ => Err(TypeMismatch)
      }
    _ => Err(NotAnEquality)
  }
}

///|
fn db_mk_eq(lhs : DbTerm, rhs : DbTerm) -> Result[DbTerm, LogicError] {
  match (db_type_of(lhs), db_type_of(rhs)) {
    (Some(ty_l), Some(ty_r)) =>
      if !ty_eq(ty_l, ty_r) {
        Err(TypeMismatch)
      } else {
        let eq_ty = fun_ty(ty_l, fun_ty(ty_l, bool_ty()))
        Ok(DbComb(DbComb(DbConst("=", eq_ty), lhs), rhs))
      }
    _ => Err(TypeMismatch)
  }
}

///|
fn db_hyps_union(a : Array[DbTerm], b : Array[DbTerm]) -> Array[DbTerm] {
  let out = a.copy()
  for h in b {
    if !out.any(fn(x) { db_term_eq(x, h) }) {
      out.push(h)
    }
  }
  out
}

///|
fn db_hyps_dedup(hs : Array[DbTerm]) -> Array[DbTerm] {
  db_hyps_union([], hs)
}

///|
fn db_hyps_remove(hs : Array[DbTerm], target : DbTerm) -> Array[DbTerm] {
  hs.filter(fn(h) { !db_term_eq(h, target) })
}

///|
fn expect_bool(term : DbTerm) -> Result[Unit, LogicError] {
  match db_type_of(term) {
    Some(ty) => if is_bool_ty(ty) { Ok(()) } else { Err(NotBoolTerm) }
    None => Err(TypeMismatch)
  }
}

///|
pub fn mk_eq(lhs : Term, rhs : Term) -> Result[Term, LogicError] {
  match (lower_term(lhs), lower_term(rhs)) {
    (Ok(l), Ok(r)) =>
      match db_mk_eq(l, r) {
        Ok(eq_db) => lift_term(eq_db)
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn dest_eq(term : Term) -> Result[(Term, Term), LogicError] {
  match lower_term(term) {
    Ok(db_t) =>
      match db_dest_eq(db_t) {
        Ok((l, r)) =>
          match (lift_term(l), lift_term(r)) {
            (Ok(l2), Ok(r2)) => Ok((l2, r2))
            _ => Err(BoundaryFailure)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn thm_hyp_count(th : Thm) -> Int {
  th.hyps.length()
}

///|
pub fn thm_hyps(th : Thm) -> Result[Array[Term], LogicError] {
  let out : Array[Term] = []
  for h in th.hyps {
    match lift_term(h) {
      Ok(v) => out.push(v)
      Err(e) => return Err(e)
    }
  }
  Ok(out)
}

///|
pub fn thm_concl(th : Thm) -> Result[Term, LogicError] {
  lift_term(th.concl)
}

///|
pub fn thm_to_string(th : Thm) -> String {
  let hs = th.hyps.map(fn(h) { db_term_to_string(h) }).join(", ")
  "[" + hs + "] |- " + db_term_to_string(th.concl)
}

///|
pub fn refl(term : Term) -> Result[Thm, LogicError] {
  match lower_term(term) {
    Ok(t) =>
      match db_mk_eq(t, t) {
        Ok(eq) => Ok(mk_thm([], eq))
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn assume(prop : Term) -> Result[Thm, LogicError] {
  match lower_term(prop) {
    Ok(p) =>
      match expect_bool(p) {
        Ok(_) => Ok(mk_thm([p], p))
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn trans(th1 : Thm, th2 : Thm) -> Result[Thm, LogicError] {
  match (db_dest_eq(th1.concl), db_dest_eq(th2.concl)) {
    (Ok((l1, r1)), Ok((l2, r2))) =>
      if !db_term_eq(r1, l2) {
        Err(AlphaMismatch)
      } else {
        match db_mk_eq(l1, r2) {
          Ok(eq) => Ok(mk_thm(db_hyps_union(th1.hyps, th2.hyps), eq))
          Err(e) => Err(e)
        }
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn mk_comb_rule(th_fg : Thm, th_xy : Thm) -> Result[Thm, LogicError] {
  match (db_dest_eq(th_fg.concl), db_dest_eq(th_xy.concl)) {
    (Ok((f, g)), Ok((x, y))) =>
      match (db_type_of(f), db_type_of(g), db_type_of(x), db_type_of(y)) {
        (Some(ty_f), Some(ty_g), Some(ty_x), Some(ty_y)) =>
          match (dest_fun_ty(ty_f), dest_fun_ty(ty_g)) {
            (Some((dom_f, cod_f)), Some((dom_g, cod_g))) =>
              if ty_eq(dom_f, ty_x) && ty_eq(dom_g, ty_y) && ty_eq(cod_f, cod_g) {
                match db_mk_eq(DbComb(f, x), DbComb(g, y)) {
                  Ok(eq) =>
                    Ok(mk_thm(db_hyps_union(th_fg.hyps, th_xy.hyps), eq))
                  Err(e) => Err(e)
                }
              } else {
                Err(TypeMismatch)
              }
            _ => Err(TypeMismatch)
          }
        _ => Err(TypeMismatch)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn abs_rule(x : Term, th : Thm) -> Result[Thm, LogicError] {
  match lower_term(x) {
    Ok(x_db) =>
      match x_db {
        DbFree(_, ty) =>
          if th.hyps.any(fn(h) { db_has_free(h, x_db) }) {
            Err(VarFreeInHyp)
          } else {
            match db_dest_eq(th.concl) {
              Ok((lhs, rhs)) =>
                match db_mk_eq(DbAbs(ty, lhs), DbAbs(ty, rhs)) {
                  Ok(eq) => Ok(mk_thm(th.hyps, eq))
                  Err(e) => Err(e)
                }
              Err(e) => Err(e)
            }
          }
        _ => Err(InvalidInstantiation)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn beta_rule(term : Term) -> Result[Thm, LogicError] {
  match lower_term(term) {
    Ok(redex) =>
      match redex {
        DbComb(DbAbs(dom, _), arg) =>
          match db_type_of(arg) {
            Some(arg_ty) =>
              if !ty_eq(dom, arg_ty) {
                Err(TypeMismatch)
              } else {
                match db_beta_reduce_once(redex) {
                  Some(out) =>
                    match db_mk_eq(redex, out) {
                      Ok(eq) => Ok(mk_thm([], eq))
                      Err(e) => Err(e)
                    }
                  None => Err(NotTrivialBetaRedex)
                }
              }
            None => Err(TypeMismatch)
          }
        _ => Err(NotTrivialBetaRedex)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn eq_mp(th_eq : Thm, th_p : Thm) -> Result[Thm, LogicError] {
  match db_dest_eq(th_eq.concl) {
    Ok((lhs, rhs)) =>
      match (expect_bool(lhs), expect_bool(rhs), expect_bool(th_p.concl)) {
        (Ok(_), Ok(_), Ok(_)) =>
          if !db_term_eq(lhs, th_p.concl) {
            Err(AlphaMismatch)
          } else {
            Ok(mk_thm(db_hyps_union(th_eq.hyps, th_p.hyps), rhs))
          }
        (Err(e), _, _) => Err(e)
        (_, Err(e), _) => Err(e)
        (_, _, Err(e)) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn deduct_antisym_rule(th1 : Thm, th2 : Thm) -> Result[Thm, LogicError] {
  match (expect_bool(th1.concl), expect_bool(th2.concl)) {
    (Ok(_), Ok(_)) =>
      match db_mk_eq(th1.concl, th2.concl) {
        Ok(eq) =>
          Ok(
            mk_thm(
              db_hyps_union(
                db_hyps_remove(th1.hyps, th2.concl),
                db_hyps_remove(th2.hyps, th1.concl),
              ),
              eq,
            ),
          )
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
fn validate_db_inst_subst(
  subst : Array[(DbTerm, DbTerm)],
) -> Result[Unit, LogicError] {
  let seen : Array[DbTerm] = []
  for pair in subst {
    let (key, value) = pair
    match key {
      DbFree(_, _) => ()
      _ => return Err(InvalidInstantiation)
    }
    if seen.any(fn(k) { db_term_eq(k, key) }) {
      return Err(InvalidInstantiation)
    }
    seen.push(key)
    match value {
      DbBound(_, _) => return Err(VariableCaptured)
      _ => ()
    }
    match (db_type_of(key), db_type_of(value)) {
      (Some(ty_k), Some(ty_v)) =>
        if !ty_eq(ty_k, ty_v) {
          return Err(TypeMismatch)
        }
      _ => return Err(TypeMismatch)
    }
  }
  Ok(())
}

///|
fn db_eq_const_type_ok(ty : HolType) -> Bool {
  match ty {
    TyApp("fun", [lhs, TyApp("fun", [rhs, TyApp("bool", [])])]) =>
      ty_eq(lhs, rhs)
    _ => false
  }
}

///|
fn db_consts_of(term : DbTerm, out : Array[(String, HolType)]) -> Unit {
  match term {
    DbBound(_, _) => ()
    DbFree(_, _) => ()
    DbConst(name, ty) => out.push((name, ty))
    DbComb(f, x) => {
      db_consts_of(f, out)
      db_consts_of(x, out)
    }
    DbAbs(_, body) => db_consts_of(body, out)
  }
}

///|
fn theorem_const_names(th : Thm) -> Array[String] {
  let consts : Array[(String, HolType)] = []
  th.hyps.each(fn(h) { db_consts_of(h, consts) })
  db_consts_of(th.concl, consts)
  let out : Array[String] = []
  for item in consts {
    let (name, _) = item
    if name != "=" && !out.contains(name) {
      out.push(name)
    }
  }
  out
}

///|
fn resolve_thm_const_ids(
  state : KernelState,
  th : Thm,
) -> Result[Array[(String, ConstId)], LogicError] {
  let names = theorem_const_names(th)
  let out : Array[(String, ConstId)] = []
  for name in names {
    match ks_lookup_const_id(state, name) {
      Some(id) => out.push((name, id))
      None => return Err(TypeMismatch)
    }
  }
  Ok(out)
}

///|
fn const_id_bindings_match(
  recorded : Array[(String, ConstId)],
  resolved : Array[(String, ConstId)],
) -> Bool {
  for pair in recorded {
    let (name, id) = pair
    let mut found = false
    for pair2 in resolved {
      let (name2, id2) = pair2
      if name == name2 {
        found = true
        if id != id2 {
          return false
        }
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
fn thm_stamp_const_ids(
  state : KernelState,
  th : Thm,
) -> Result[Thm, LogicError] {
  match resolve_thm_const_ids(state, th) {
    Ok(ids) => Ok(thm_with_const_ids(th, ids))
    Err(e) => Err(e)
  }
}

///|
pub fn thm_bind_const_ids(
  state : KernelState,
  th : Thm,
) -> Result[Thm, LogicError] {
  match thm_stamp_const_ids(state, th) {
    Ok(stamped) =>
      match ensure_thm_admissible(state, stamped) {
        Ok(_) => Ok(stamped)
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
fn theorem_const_instances_ok(state : KernelState, th : Thm) -> Bool {
  let consts : Array[(String, HolType)] = []
  th.hyps.each(fn(h) { db_consts_of(h, consts) })
  db_consts_of(th.concl, consts)
  for item in consts {
    let (name, inst_ty) = item
    if name == "=" {
      if !db_eq_const_type_ok(inst_ty) {
        return false
      }
    } else {
      match ks_const_schema(state, name) {
        Some(schema_ty) =>
          if !ty_is_instance_of(inst_ty, schema_ty) {
            return false
          }
        None => return false
      }
    }
  }
  true
}

///|
fn theorem_def_inst_coherent(state : KernelState, th : Thm) -> Bool {
  match th.def_origin {
    None => true
    Some(name) =>
      if !ks_has_def_head(state, name) || th.hyps.length() != 0 {
        false
      } else {
        match db_dest_eq(th.concl) {
          Ok((lhs, rhs)) =>
            match lhs {
              DbConst(lhs_name, lhs_ty) =>
                if lhs_name != name {
                  false
                } else {
                  match lift_term(rhs) {
                    Ok(rhs_term) => term_tyvars_subset(rhs_term, lhs_ty)
                    Err(_) => false
                  }
                }
              _ => false
            }
          Err(_) => false
        }
      }
  }
}

///|
fn ensure_thm_admissible(
  state : KernelState,
  th : Thm,
) -> Result[Unit, LogicError] {
  let names = theorem_const_names(th)
  match resolve_thm_const_ids(state, th) {
    Ok(resolved_ids) => {
      if names.length() > 0 && th.const_ids.length() == 0 {
        return Err(InvalidInstantiation)
      }
      if th.const_ids.length() > 0 &&
        !const_id_bindings_match(th.const_ids, resolved_ids) {
        return Err(InvalidInstantiation)
      }
    }
    Err(e) => return Err(e)
  }
  if !theorem_const_instances_ok(state, th) {
    return Err(TypeMismatch)
  }
  if !theorem_def_inst_coherent(state, th) {
    return Err(InvalidInstantiation)
  }
  Ok(())
}

///|
pub fn thm_is_admissible(state : KernelState, th : Thm) -> Bool {
  match ensure_thm_admissible(state, th) {
    Ok(_) => true
    Err(_) => false
  }
}

///|
pub fn refl_checked(
  state : KernelState,
  term : Term,
) -> Result[Thm, LogicError] {
  match refl(term) {
    Ok(th) =>
      match thm_stamp_const_ids(state, th) {
        Ok(stamped) =>
          match ensure_thm_admissible(state, stamped) {
            Ok(_) => Ok(stamped)
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn assume_checked(
  state : KernelState,
  prop : Term,
) -> Result[Thm, LogicError] {
  match assume(prop) {
    Ok(th) =>
      match thm_stamp_const_ids(state, th) {
        Ok(stamped) =>
          match ensure_thm_admissible(state, stamped) {
            Ok(_) => Ok(stamped)
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn trans_checked(
  state : KernelState,
  th1 : Thm,
  th2 : Thm,
) -> Result[Thm, LogicError] {
  match (ensure_thm_admissible(state, th1), ensure_thm_admissible(state, th2)) {
    (Ok(_), Ok(_)) =>
      match trans(th1, th2) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn mk_comb_rule_checked(
  state : KernelState,
  th_fg : Thm,
  th_xy : Thm,
) -> Result[Thm, LogicError] {
  match
    (ensure_thm_admissible(state, th_fg), ensure_thm_admissible(state, th_xy)) {
    (Ok(_), Ok(_)) =>
      match mk_comb_rule(th_fg, th_xy) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn abs_rule_checked(
  state : KernelState,
  x : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  match ensure_thm_admissible(state, th) {
    Ok(_) =>
      match abs_rule(x, th) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn beta_rule_checked(
  state : KernelState,
  term : Term,
) -> Result[Thm, LogicError] {
  match beta_rule(term) {
    Ok(out) =>
      match thm_stamp_const_ids(state, out) {
        Ok(stamped) =>
          match ensure_thm_admissible(state, stamped) {
            Ok(_) => Ok(stamped)
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn eq_mp_checked(
  state : KernelState,
  th_eq : Thm,
  th_p : Thm,
) -> Result[Thm, LogicError] {
  match
    (ensure_thm_admissible(state, th_eq), ensure_thm_admissible(state, th_p)) {
    (Ok(_), Ok(_)) =>
      match eq_mp(th_eq, th_p) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
pub fn deduct_antisym_rule_checked(
  state : KernelState,
  th1 : Thm,
  th2 : Thm,
) -> Result[Thm, LogicError] {
  match (ensure_thm_admissible(state, th1), ensure_thm_admissible(state, th2)) {
    (Ok(_), Ok(_)) =>
      match deduct_antisym_rule(th1, th2) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    (Err(e), _) => Err(e)
    (_, Err(e)) => Err(e)
  }
}

///|
fn inst_type_core_checked(
  state : KernelState,
  subst : Array[(String, HolType)],
  th : Thm,
) -> Result[Thm, LogicError] {
  if has_duplicate_ty_subst_keys(subst) {
    return Err(InvalidInstantiation)
  }
  if !ks_type_subst_is_admissible(state, subst) {
    return Err(InvalidInstantiation)
  }
  let out = mk_thm_with_origin(
    th.hyps.map(fn(h) { db_apply_ty_subst(subst, h) }),
    db_apply_ty_subst(subst, th.concl),
    th.def_origin,
  )
  if !theorem_const_instances_ok(state, out) {
    return Err(TypeMismatch)
  }
  if !theorem_def_inst_coherent(state, out) {
    return Err(InvalidInstantiation)
  }
  Ok(out)
}

///|
/// Type instantiation must be checked against kernel state admissibility.
pub fn inst_type(
  state : KernelState,
  subst : Array[(String, HolType)],
  th : Thm,
) -> Result[Thm, LogicError] {
  match ensure_thm_admissible(state, th) {
    Ok(_) =>
      match inst_type_core_checked(state, subst, th) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn inst(subst : Array[(Term, Term)], th : Thm) -> Result[Thm, LogicError] {
  let db_subst : Array[(DbTerm, DbTerm)] = []
  for pair in subst {
    let (key, value) = pair
    match (lower_term(key), lower_term(value)) {
      (Ok(k), Ok(v)) => db_subst.push((k, v))
      _ => return Err(BoundaryFailure)
    }
  }
  match validate_db_inst_subst(db_subst) {
    Ok(_) =>
      Ok(
        mk_thm_with_origin(
          th.hyps.map(fn(h) { db_subst_free_parallel(h, db_subst) }),
          db_subst_free_parallel(th.concl, db_subst),
          th.def_origin,
        ),
      )
    Err(e) => Err(e)
  }
}

///|
pub fn inst_checked(
  state : KernelState,
  subst : Array[(Term, Term)],
  th : Thm,
) -> Result[Thm, LogicError] {
  match ensure_thm_admissible(state, th) {
    Ok(_) =>
      match inst(subst, th) {
        Ok(out) =>
          match thm_stamp_const_ids(state, out) {
            Ok(stamped) =>
              match ensure_thm_admissible(state, stamped) {
                Ok(_) => Ok(stamped)
                Err(e) => Err(e)
              }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn kernel_thm_phase0_ready() -> Bool {
  true
}
