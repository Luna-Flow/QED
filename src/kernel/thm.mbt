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
fn is_valid_term_subst(subst : Array[(Term, Term)]) -> Bool {
  let keys : Array[DbTerm] = []
  for pair in subst {
    let (k, v) = pair
    match (to_db_term(k), to_db_term(v)) {
      (Some(k_db), Some(v_db)) =>
        match k_db {
          DbFree(_, _) => {
            if !ty_eq(type_of(k), type_of(v)) {
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
      _ => return false
    }
  }
  true
}

///|
/// Theorem constructors and primitive rules
pub fn mk_eq(lhs : Term, rhs : Term) -> Term {
  let eq_ty = fun_ty(type_of(lhs), fun_ty(type_of(rhs), bool_ty()))
  let eq_const = mk_const("=", eq_ty)
  mk_comb(mk_comb(eq_const, lhs), rhs)
}

///|
pub fn dest_eq(t : Term) -> (Term, Term)? {
  match t {
    Comb(Comb(Const("=", _), lhs), rhs) => Some((lhs, rhs))
    _ => None
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
      for h in hs {
        match from_db_term(h) {
          Some(h2) => hs2.push(h2)
          None => return None
        }
      }
      match from_db_term(c) {
        Some(c2) => Some(Sequent(hyps_dedup(hs2), c2))
        None => None
      }
    }
  }
}

///|
pub fn refl(t : Term) -> Thm {
  Sequent([], mk_eq(t, t))
}

///|
pub fn assume(p : Term) -> Thm? {
  if is_bool_ty(type_of(p)) {
    Some(Sequent([p], p))
  } else {
    None
  }
}

///|
fn hyps_union(a : Array[Term], b : Array[Term]) -> Array[Term] {
  let out = a.copy()
  for h in b {
    if !out.any(fn(x) { term_alpha_eq(x, h) }) {
      out.push(h)
    }
  }
  out
}

///|
fn hyps_dedup(hs : Array[Term]) -> Array[Term] {
  hyps_union([], hs)
}

///|
fn hyps_remove(hs : Array[Term], t : Term) -> Array[Term] {
  hs.filter(fn(h) { !term_alpha_eq(h, t) })
}

///|
pub fn trans(th1 : Thm, th2 : Thm) -> Thm? {
  match (thm_to_db(th1), thm_to_db(th2)) {
    (Some(DbSeq(h1, c1)), Some(DbSeq(h2, c2))) =>
      match (db_dest_eq(c1), db_dest_eq(c2)) {
        (Some((l1, r1)), Some((l2, r2))) =>
          if db_term_eq(r1, l2) {
            match db_to_thm(DbSeq(db_hyps_union(h1, h2), db_mk_eq(l1, r2))) {
              Some(th) => Some(th)
              None => None
            }
          } else {
            None
          }
        _ => None
      }
    _ => None
  }
}

///|
pub fn abs_rule(x : Term, th : Thm) -> Thm? {
  match (to_db_term(x), thm_to_db(th)) {
    (Some(x_db), Some(DbSeq(hs, concl))) =>
      match x_db {
        DbFree(_, ty) =>
          if hs.any(fn(h) { db_has_free(h, x_db) }) {
            None
          } else {
            match db_dest_eq(concl) {
              Some((l, r)) =>
                db_to_thm(DbSeq(hs, db_mk_eq(DbAbs(ty, l), DbAbs(ty, r))))
              _ => None
            }
          }
        _ => None
      }
    _ => None
  }
}

///|
pub fn beta_rule(t : Term) -> Thm? {
  match to_db_term(t) {
    Some(db_t) =>
      match db_t {
        DbComb(DbAbs(dom, _), arg) =>
          if !ty_eq(dom, db_type_of(arg)) {
            None
          } else {
            match db_beta_reduce_once(db_t) {
              Some(db_out) =>
                match from_db_term(db_out) {
                  Some(out) => Some(Sequent([], mk_eq(t, out)))
                  None => None
                }
              None => None
            }
          }
        _ => None
      }
    None => None
  }
}

///|
pub fn eq_mp(th_eq : Thm, th_p : Thm) -> Thm? {
  match (thm_to_db(th_eq), thm_to_db(th_p)) {
    (Some(DbSeq(h_eq, c_eq)), Some(DbSeq(h_p, c_p))) =>
      match db_dest_eq(c_eq) {
        Some((lhs, rhs)) => {
          let ok_l = is_bool_ty(db_type_of(lhs))
          let ok_r = is_bool_ty(db_type_of(rhs))
          let ok_m = db_term_eq(lhs, c_p)
          let ok = ok_l && ok_r && ok_m
          if ok {
            db_to_thm(DbSeq(db_hyps_union(h_eq, h_p), rhs))
          } else {
            None
          }
        }
        None => None
      }
    _ => None
  }
}

///|
pub fn deduct_antisym_rule(th1 : Thm, th2 : Thm) -> Thm {
  match th1 {
    Sequent(h1, p) =>
      match th2 {
        Sequent(h2, q) => {
          let h1p = hyps_remove(h1, q)
          let h2p = hyps_remove(h2, p)
          Sequent(hyps_union(h1p, h2p), mk_eq(p, q))
        }
      }
  }
}

///|
pub fn inst_type(subst : Array[(String, HolType)], th : Thm) -> Thm? {
  if has_duplicate_ty_subst_keys(subst) {
    return None
  }
  match thm_to_db(th) {
    Some(DbSeq(hs, c)) =>
      db_to_thm(
        DbSeq(
          hs.map(fn(h) { db_apply_ty_subst(subst, h) }),
          db_apply_ty_subst(subst, c),
        ),
      )
    None => None
  }
}

///|
pub fn inst(subst : Array[(Term, Term)], th : Thm) -> Thm? {
  if !is_valid_term_subst(subst) {
    return None
  }
  let db_subst : Array[(DbTerm, DbTerm)] = []
  for pair in subst {
    let (k, v) = pair
    match (to_db_term(k), to_db_term(v)) {
      (Some(k_db), Some(v_db)) => db_subst.push((k_db, v_db))
      _ => return None
    }
  }
  match thm_to_db(th) {
    Some(DbSeq(hs, c)) =>
      db_to_thm(
        DbSeq(
          hs.map(fn(h) { db_subst_free_parallel(h, db_subst) }),
          db_subst_free_parallel(c, db_subst),
        ),
      )
    None => None
  }
}

///|
pub fn mk_comb_rule(th_fg : Thm, th_xy : Thm) -> Thm? {
  match (thm_to_db(th_fg), thm_to_db(th_xy)) {
    (Some(DbSeq(hfg, cfg)), Some(DbSeq(hxy, cxy))) =>
      match (db_dest_eq(cfg), db_dest_eq(cxy)) {
        (Some((f, g)), Some((x, y))) =>
          match (dest_fun_ty(db_type_of(f)), dest_fun_ty(db_type_of(g))) {
            (Some((dom_f, cod_f)), Some((dom_g, cod_g))) => {
              let ok_dom_f = ty_eq(dom_f, db_type_of(x))
              let ok_dom_g = ty_eq(dom_g, db_type_of(y))
              let ok_cod = ty_eq(cod_f, cod_g)
              let ok = ok_dom_f && ok_dom_g && ok_cod
              if ok {
                db_to_thm(
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
    _ => None
  }
}

///|
pub fn kernel_thm_phase0_ready() -> Bool {
  true
}
