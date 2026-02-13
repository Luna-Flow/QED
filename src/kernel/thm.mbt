///|
/// Theorem object and primitive rule placeholders for kernel phase 1.
pub enum Thm {
  Sequent(Array[Term], Term)
}

///|
priv enum DbSequent {
  DbSeq(Array[DbTerm], DbTerm)
}

///|
/// Type-substitution helpers
fn has_duplicate_ty_subst_keys(subst : Array[(String, HolType)]) -> Bool {
  let seen : Array[String] = []
  for kv in subst {
    let (k, _) = kv
    if seen.contains(k) {
      return true
    }
    seen.push(k)
  }
  false
}

///|
/// Term-substitution helpers
fn is_valid_db_term_subst(subst : Array[(DbTerm, DbTerm)]) -> Bool {
  let keys : Array[DbTerm] = []
  for pair in subst {
    let (k_db, v_db) = pair
    match k_db {
      DbFree(_, _) => {
        match (db_type_of(k_db), db_type_of(v_db)) {
          (Some(ty_k), Some(ty_v)) => if !ty_eq(ty_k, ty_v) { return false }
          _ => return false
        }
        if keys.any(fn(x) { db_term_eq(x, k_db) }) {
          return false
        }
        keys.push(k_db)
        match v_db {
          DbBound(_, _) => return false
          _ => ()
        }
      }
      _ => return false
    }
  }
  true
}

///|
/// Theorem constructors and primitive rules
pub fn mk_eq(lhs : Term, rhs : Term) -> Term? {
  let mk_named = fn() -> Term? {
    match (type_of(lhs), type_of(rhs)) {
      (Some(ty_l), Some(ty_r)) => {
        let eq_ty = fun_ty(ty_l, fun_ty(ty_r, bool_ty()))
        let eq_const = mk_const("=", eq_ty)
        Some(mk_comb(mk_comb(eq_const, lhs), rhs))
      }
      _ => None
    }
  }
  match (to_db_term(lhs), to_db_term(rhs)) {
    (Some(l), Some(r)) =>
      match db_mk_eq(l, r) {
        Some(db_eq) =>
          match from_db_term(db_eq) {
            Some(t) => Some(t)
            None => mk_named()
          }
        None => mk_named()
      }
    _ => mk_named()
  }
}

///|
pub fn dest_eq(t : Term) -> (Term, Term)? {
  match to_db_term(t) {
    Some(db_t) =>
      match db_dest_eq(db_t) {
        Some((l, r)) =>
          match (from_db_term(l), from_db_term(r)) {
            (Some(l2), Some(r2)) => Some((l2, r2))
            _ => None
          }
        None => None
      }
    None => None
  }
}

///|
fn db_dest_eq(t : DbTerm) -> (DbTerm, DbTerm)? {
  match t {
    DbComb(DbComb(DbConst("=", _), lhs), rhs) => Some((lhs, rhs))
    _ => None
  }
}

///|
fn db_mk_eq(lhs : DbTerm, rhs : DbTerm) -> DbTerm? {
  match (db_type_of(lhs), db_type_of(rhs)) {
    (Some(ty_l), Some(ty_r)) => {
      let eq_ty = fun_ty(ty_l, fun_ty(ty_r, bool_ty()))
      Some(DbComb(DbComb(DbConst("=", eq_ty), lhs), rhs))
    }
    _ => None
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
fn thm_to_db(th : Thm) -> DbSequent? {
  match th {
    Sequent(hs, c) => {
      let hs2 : Array[DbTerm] = []
      for h in hs {
        match to_db_term(h) {
          Some(h_db) => hs2.push(h_db)
          None => return None
        }
      }
      match to_db_term(c) {
        Some(c_db) => Some(DbSeq(hs2, c_db))
        None => None
      }
    }
  }
}

///|
fn db_to_thm(db_th : DbSequent) -> Thm? {
  match db_th {
    DbSeq(hs, c) => {
      let hs2 : Array[Term] = []
      for h in db_hyps_dedup(hs) {
        match from_db_term(h) {
          Some(h2) => hs2.push(h2)
          None => return None
        }
      }
      match from_db_term(c) {
        Some(c2) => Some(Sequent(hs2, c2))
        None => None
      }
    }
  }
}

///|
fn lift_db_rule1(th : Thm, rule : (DbSequent) -> DbSequent?) -> Thm? {
  match thm_to_db(th) {
    Some(db_th) =>
      match rule(db_th) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    None => None
  }
}

///|
fn lift_db_rule2(
  th1 : Thm,
  th2 : Thm,
  rule : (DbSequent, DbSequent) -> DbSequent?,
) -> Thm? {
  match (thm_to_db(th1), thm_to_db(th2)) {
    (Some(db1), Some(db2)) =>
      match rule(db1, db2) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    _ => None
  }
}

///|
fn lift_db_term_rule(t : Term, rule : (DbTerm) -> DbSequent?) -> Thm? {
  match to_db_term(t) {
    Some(db_t) =>
      match rule(db_t) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    None => None
  }
}

///|
fn lift_db_term_thm_rule(
  t : Term,
  th : Thm,
  rule : (DbTerm, DbSequent) -> DbSequent?,
) -> Thm? {
  match (to_db_term(t), thm_to_db(th)) {
    (Some(db_t), Some(db_th)) =>
      match rule(db_t, db_th) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    _ => None
  }
}

///|
pub fn refl(t : Term) -> Thm? {
  match to_db_term(t) {
    Some(db_t) =>
      match db_rule_refl(db_t) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    None => None
  }
}

///|
pub fn assume(p : Term) -> Thm? {
  match to_db_term(p) {
    Some(db_p) =>
      match db_rule_assume(db_p) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    None => None
  }
}

///|
fn db_hyps_remove(hs : Array[DbTerm], t : DbTerm) -> Array[DbTerm] {
  hs.filter(fn(h) { !db_term_eq(h, t) })
}

///|
fn db_rule_trans(th1 : DbSequent, th2 : DbSequent) -> DbSequent? {
  match (th1, th2) {
    (DbSeq(h1, c1), DbSeq(h2, c2)) =>
      match (db_dest_eq(c1), db_dest_eq(c2)) {
        (Some((l1, r1)), Some((l2, r2))) =>
          if db_term_eq(r1, l2) {
            match db_mk_eq(l1, r2) {
              Some(eq) => Some(DbSeq(db_hyps_union(h1, h2), eq))
              None => None
            }
          } else {
            None
          }
        _ => None
      }
  }
}

///|
fn db_rule_eq_mp(th_eq : DbSequent, th_p : DbSequent) -> DbSequent? {
  match (th_eq, th_p) {
    (DbSeq(h_eq, c_eq), DbSeq(h_p, c_p)) =>
      match db_dest_eq(c_eq) {
        Some((lhs, rhs)) =>
          match (db_type_of(lhs), db_type_of(rhs)) {
            (Some(ty_l), Some(ty_r)) => {
              let ok_l = is_bool_ty(ty_l)
              let ok_r = is_bool_ty(ty_r)
              let ok_m = db_term_eq(lhs, c_p)
              let ok = ok_l && ok_r && ok_m
              if ok {
                Some(DbSeq(db_hyps_union(h_eq, h_p), rhs))
              } else {
                None
              }
            }
            _ => None
          }
        None => None
      }
  }
}

///|
fn db_rule_mk_comb(th_fg : DbSequent, th_xy : DbSequent) -> DbSequent? {
  match (th_fg, th_xy) {
    (DbSeq(hfg, cfg), DbSeq(hxy, cxy)) =>
      match (db_dest_eq(cfg), db_dest_eq(cxy)) {
        (Some((f, g)), Some((x, y))) =>
          match (db_type_of(f), db_type_of(g), db_type_of(x), db_type_of(y)) {
            (Some(ty_f), Some(ty_g), Some(ty_x), Some(ty_y)) =>
              match (dest_fun_ty(ty_f), dest_fun_ty(ty_g)) {
                (Some((dom_f, cod_f)), Some((dom_g, cod_g))) => {
                  let ok_dom_f = ty_eq(dom_f, ty_x)
                  let ok_dom_g = ty_eq(dom_g, ty_y)
                  let ok_cod = ty_eq(cod_f, cod_g)
                  let ok = ok_dom_f && ok_dom_g && ok_cod
                  if ok {
                    match db_mk_eq(DbComb(f, x), DbComb(g, y)) {
                      Some(eq) => Some(DbSeq(db_hyps_union(hfg, hxy), eq))
                      None => None
                    }
                  } else {
                    None
                  }
                }
                _ => None
              }
            _ => None
          }
        _ => None
      }
  }
}

///|
fn db_rule_abs(x : DbTerm, th : DbSequent) -> DbSequent? {
  match (x, th) {
    (DbFree(_, ty), DbSeq(hs, concl)) =>
      if hs.any(fn(h) { db_has_free(h, x) }) {
        None
      } else {
        match db_dest_eq(concl) {
          Some((l, r)) =>
            match db_mk_eq(DbAbs(ty, l), DbAbs(ty, r)) {
              Some(eq) => Some(DbSeq(hs, eq))
              None => None
            }
          _ => None
        }
      }
    _ => None
  }
}

///|
fn db_rule_beta(t : DbTerm) -> DbSequent? {
  match t {
    DbComb(DbAbs(dom, _), arg) =>
      match db_type_of(arg) {
        Some(arg_ty) =>
          if !ty_eq(dom, arg_ty) {
            None
          } else {
            match db_beta_reduce_once(t) {
              Some(out) =>
                match db_mk_eq(t, out) {
                  Some(eq) => Some(DbSeq([], eq))
                  None => None
                }
              None => None
            }
          }
        None => None
      }
    _ => None
  }
}

///|
fn db_rule_inst_type(
  subst : Array[(String, HolType)],
  th : DbSequent,
) -> DbSequent {
  match th {
    DbSeq(hs, c) =>
      DbSeq(
        hs.map(fn(h) { db_apply_ty_subst(subst, h) }),
        db_apply_ty_subst(subst, c),
      )
  }
}

///|
fn db_rule_inst(subst : Array[(DbTerm, DbTerm)], th : DbSequent) -> DbSequent {
  match th {
    DbSeq(hs, c) =>
      DbSeq(
        hs.map(fn(h) { db_subst_free_parallel(h, subst) }),
        db_subst_free_parallel(c, subst),
      )
  }
}

///|
fn db_rule_deduct_antisym(th1 : DbSequent, th2 : DbSequent) -> DbSequent? {
  match (th1, th2) {
    (DbSeq(h1, p), DbSeq(h2, q)) =>
      match db_mk_eq(p, q) {
        Some(eq) =>
          Some(
            DbSeq(
              db_hyps_union(db_hyps_remove(h1, q), db_hyps_remove(h2, p)),
              eq,
            ),
          )
        None => None
      }
  }
}

///|
fn db_rule_refl(t : DbTerm) -> DbSequent? {
  match db_mk_eq(t, t) {
    Some(eq) => Some(DbSeq([], eq))
    None => None
  }
}

///|
fn db_rule_assume(p : DbTerm) -> DbSequent? {
  match db_type_of(p) {
    Some(ty) => if is_bool_ty(ty) { Some(DbSeq([p], p)) } else { None }
    None => None
  }
}

///|
pub fn trans(th1 : Thm, th2 : Thm) -> Thm? {
  lift_db_rule2(th1, th2, db_rule_trans)
}

///|
pub fn abs_rule(x : Term, th : Thm) -> Thm? {
  lift_db_term_thm_rule(x, th, db_rule_abs)
}

///|
pub fn beta_rule(t : Term) -> Thm? {
  lift_db_term_rule(t, db_rule_beta)
}

///|
pub fn eq_mp(th_eq : Thm, th_p : Thm) -> Thm? {
  lift_db_rule2(th_eq, th_p, db_rule_eq_mp)
}

///|
pub fn deduct_antisym_rule(th1 : Thm, th2 : Thm) -> Thm? {
  lift_db_rule2(th1, th2, db_rule_deduct_antisym)
}

///|
pub fn inst_type(subst : Array[(String, HolType)], th : Thm) -> Thm? {
  if has_duplicate_ty_subst_keys(subst) {
    return None
  }
  lift_db_rule1(th, fn(db_th) { Some(db_rule_inst_type(subst, db_th)) })
}

///|
pub fn inst(subst : Array[(Term, Term)], th : Thm) -> Thm? {
  let db_subst : Array[(DbTerm, DbTerm)] = []
  for pair in subst {
    let (k, v) = pair
    match (to_db_term(k), to_db_term(v)) {
      (Some(k_db), Some(v_db)) => db_subst.push((k_db, v_db))
      _ => return None
    }
  }
  if !is_valid_db_term_subst(db_subst) {
    return None
  }
  lift_db_rule1(th, fn(db_th) { Some(db_rule_inst(db_subst, db_th)) })
}

///|
pub fn mk_comb_rule(th_fg : Thm, th_xy : Thm) -> Thm? {
  lift_db_rule2(th_fg, th_xy, db_rule_mk_comb)
}

///|
pub fn kernel_thm_phase0_ready() -> Bool {
  true
}
