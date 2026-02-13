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
        if !ty_eq(db_type_of(k_db), db_type_of(v_db)) {
          return false
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
pub fn mk_eq(lhs : Term, rhs : Term) -> Term {
  match (to_db_term(lhs), to_db_term(rhs)) {
    (Some(l), Some(r)) =>
      match from_db_term(db_mk_eq(l, r)) {
        Some(t) => t
        None => {
          let eq_ty = fun_ty(type_of(lhs), fun_ty(type_of(rhs), bool_ty()))
          let eq_const = mk_const("=", eq_ty)
          mk_comb(mk_comb(eq_const, lhs), rhs)
        }
      }
    _ => {
      let eq_ty = fun_ty(type_of(lhs), fun_ty(type_of(rhs), bool_ty()))
      let eq_const = mk_const("=", eq_ty)
      mk_comb(mk_comb(eq_const, lhs), rhs)
    }
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
fn ty_eq(t1 : HolType, t2 : HolType) -> Bool {
  hol_type_to_string(t1) == hol_type_to_string(t2)
}

///|
fn db_dest_eq(t : DbTerm) -> (DbTerm, DbTerm)? {
  match t {
    DbComb(DbComb(DbConst("=", _), lhs), rhs) => Some((lhs, rhs))
    _ => None
  }
}

///|
fn db_mk_eq(lhs : DbTerm, rhs : DbTerm) -> DbTerm {
  let eq_ty = fun_ty(db_type_of(lhs), fun_ty(db_type_of(rhs), bool_ty()))
  DbComb(DbComb(DbConst("=", eq_ty), lhs), rhs)
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
fn db_to_thm_or(db_th : DbSequent, fallback : Thm) -> Thm {
  match db_to_thm(db_th) {
    Some(th) => th
    None => fallback
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
pub fn refl(t : Term) -> Thm {
  match to_db_term(t) {
    Some(db_t) => db_to_thm_or(db_rule_refl(db_t), Sequent([], mk_eq(t, t)))
    None => Sequent([], mk_eq(t, t))
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
            Some(DbSeq(db_hyps_union(h1, h2), db_mk_eq(l1, r2)))
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
        Some((lhs, rhs)) => {
          let ok_l = is_bool_ty(db_type_of(lhs))
          let ok_r = is_bool_ty(db_type_of(rhs))
          let ok_m = db_term_eq(lhs, c_p)
          let ok = ok_l && ok_r && ok_m
          if ok {
            Some(DbSeq(db_hyps_union(h_eq, h_p), rhs))
          } else {
            None
          }
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
          match (dest_fun_ty(db_type_of(f)), dest_fun_ty(db_type_of(g))) {
            (Some((dom_f, cod_f)), Some((dom_g, cod_g))) => {
              let ok_dom_f = ty_eq(dom_f, db_type_of(x))
              let ok_dom_g = ty_eq(dom_g, db_type_of(y))
              let ok_cod = ty_eq(cod_f, cod_g)
              let ok = ok_dom_f && ok_dom_g && ok_cod
              if ok {
                Some(
                  DbSeq(
                    db_hyps_union(hfg, hxy),
                    db_mk_eq(DbComb(f, x), DbComb(g, y)),
                  ),
                )
              } else {
                None
              }
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
          Some((l, r)) => Some(DbSeq(hs, db_mk_eq(DbAbs(ty, l), DbAbs(ty, r))))
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
      if !ty_eq(dom, db_type_of(arg)) {
        None
      } else {
        match db_beta_reduce_once(t) {
          Some(out) => Some(DbSeq([], db_mk_eq(t, out)))
          None => None
        }
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
fn db_rule_deduct_antisym(th1 : DbSequent, th2 : DbSequent) -> DbSequent {
  match (th1, th2) {
    (DbSeq(h1, p), DbSeq(h2, q)) =>
      DbSeq(
        db_hyps_union(db_hyps_remove(h1, q), db_hyps_remove(h2, p)),
        db_mk_eq(p, q),
      )
  }
}

///|
fn db_rule_refl(t : DbTerm) -> DbSequent {
  DbSeq([], db_mk_eq(t, t))
}

///|
fn db_rule_assume(p : DbTerm) -> DbSequent? {
  if is_bool_ty(db_type_of(p)) {
    Some(DbSeq([p], p))
  } else {
    None
  }
}

///|
pub fn trans(th1 : Thm, th2 : Thm) -> Thm? {
  lift_db_rule2(th1, th2, db_rule_trans)
}

///|
pub fn abs_rule(x : Term, th : Thm) -> Thm? {
  match (to_db_term(x), thm_to_db(th)) {
    (Some(x_db), Some(db_th)) =>
      match db_rule_abs(x_db, db_th) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    _ => None
  }
}

///|
pub fn beta_rule(t : Term) -> Thm? {
  match to_db_term(t) {
    Some(db_t) =>
      match db_rule_beta(db_t) {
        Some(db_out) => db_to_thm(db_out)
        None => None
      }
    None => None
  }
}

///|
pub fn eq_mp(th_eq : Thm, th_p : Thm) -> Thm? {
  lift_db_rule2(th_eq, th_p, db_rule_eq_mp)
}

///|
pub fn deduct_antisym_rule(th1 : Thm, th2 : Thm) -> Thm {
  fn named_fallback(a : Thm, b : Thm) -> Thm {
    fn remove_h(hs : Array[Term], t : Term) -> Array[Term] {
      hs.filter(fn(h) { !term_alpha_eq(h, t) })
    }
    fn union_h(x : Array[Term], y : Array[Term]) -> Array[Term] {
      let out = x.copy()
      for h in y {
        if !out.any(fn(k) { term_alpha_eq(k, h) }) {
          out.push(h)
        }
      }
      out
    }
    match a {
      Sequent(h1, p) =>
        match b {
          Sequent(h2, q) =>
            Sequent(union_h(remove_h(h1, q), remove_h(h2, p)), mk_eq(p, q))
        }
    }
  }

  match (thm_to_db(th1), thm_to_db(th2)) {
    (Some(db1), Some(db2)) =>
      db_to_thm_or(db_rule_deduct_antisym(db1, db2), named_fallback(th1, th2))
    _ => named_fallback(th1, th2)
  }
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
