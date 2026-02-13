///|
/// Theorem object and primitive rule placeholders for kernel phase 1.
pub enum Thm {
  Sequent(Array[Term], Term)
}

///|
/// Type-substitution helpers
fn lookup_ty_subst(subst : Array[(String, HolType)], name : String) -> HolType? {
  for kv in subst {
    let (k, v) = kv
    if k == name {
      return Some(v)
    }
  }
  None
}

///|
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
fn apply_ty_subst_to_type(
  subst : Array[(String, HolType)],
  ty : HolType,
) -> HolType {
  match ty {
    TyVal(name) =>
      match lookup_ty_subst(subst, name) {
        Some(t) => t
        None => ty
      }
    TyApp(tycon, args) =>
      TyApp(tycon, args.map(fn(a) { apply_ty_subst_to_type(subst, a) }))
  }
}

///|
fn apply_ty_subst_to_term(subst : Array[(String, HolType)], t : Term) -> Term {
  match t {
    Var(name, ty) => Var(name, apply_ty_subst_to_type(subst, ty))
    Const(name, ty) => Const(name, apply_ty_subst_to_type(subst, ty))
    Comb(f, x) =>
      Comb(apply_ty_subst_to_term(subst, f), apply_ty_subst_to_term(subst, x))
    Abs(v, body) =>
      Abs(apply_ty_subst_to_term(subst, v), apply_ty_subst_to_term(subst, body))
  }
}

///|
/// Term-substitution helpers
fn lookup_term_subst(subst : Array[(Term, Term)], src : Term) -> Term? {
  for pair in subst {
    let (k, v) = pair
    if alpha_eq(k, src) {
      return Some(v)
    }
  }
  None
}

///|
fn is_valid_term_subst(subst : Array[(Term, Term)]) -> Bool {
  let keys : Array[Term] = []
  for pair in subst {
    let (k, v) = pair
    if !is_var(k) {
      return false
    }
    if !ty_eq(type_of(k), type_of(v)) {
      return false
    }
    if keys.any(fn(x) { alpha_eq(x, k) }) {
      return false
    }
    keys.push(k)
  }
  true
}

///|
fn apply_term_subst_to_term(subst : Array[(Term, Term)], t : Term) -> Term {
  fn vfree_local(v : Term, tm : Term) -> Bool {
    match tm {
      Var(_, _) => alpha_eq(v, tm)
      Const(_, _) => false
      Comb(f, x) => vfree_local(v, f) || vfree_local(v, x)
      Abs(bv, body) =>
        if alpha_eq(v, bv) {
          false
        } else {
          vfree_local(v, body)
        }
    }
  }

  match lookup_term_subst(subst, t) {
    Some(v) => v
    None =>
      match t {
        Var(_, _) => t
        Const(_, _) => t
        Comb(f, x) =>
          Comb(
            apply_term_subst_to_term(subst, f),
            apply_term_subst_to_term(subst, x),
          )
        Abs(v, body) => {
          let should_block = subst.any(fn(pair) {
            let (k, val) = pair
            !alpha_eq(k, v) && vfree_local(k, body) && vfree_local(v, val)
          })
          if should_block {
            Abs(v, body)
          } else {
            let subst2 = subst.filter(fn(pair) {
              let (k, _) = pair
              !alpha_eq(k, v)
            })
            Abs(v, apply_term_subst_to_term(subst2, body))
          }
        }
      }
  }
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
fn alpha_eq(t1 : Term, t2 : Term) -> Bool {
  db_string(t1) == db_string(t2)
}

///|
fn ty_eq(t1 : HolType, t2 : HolType) -> Bool {
  hol_type_to_string(t1) == hol_type_to_string(t2)
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
    if !out.any(fn(x) { alpha_eq(x, h) }) {
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
  hs.filter(fn(h) { !alpha_eq(h, t) })
}

///|
fn vfree_in(v : Term, t : Term) -> Bool {
  match t {
    Var(_, _) => alpha_eq(v, t)
    Const(_, _) => false
    Comb(f, x) => vfree_in(v, f) || vfree_in(v, x)
    Abs(bv, body) => if alpha_eq(v, bv) { false } else { vfree_in(v, body) }
  }
}

///|
fn vfree_in_hyps(v : Term, hs : Array[Term]) -> Bool {
  hs.any(fn(h) { vfree_in(v, h) })
}

///|
fn subst_var_safe(v : Term, repl : Term, t : Term) -> Term? {
  match t {
    Var(_, _) => if alpha_eq(t, v) { Some(repl) } else { Some(t) }
    Const(_, _) => Some(t)
    Comb(f, x) =>
      match (subst_var_safe(v, repl, f), subst_var_safe(v, repl, x)) {
        (Some(f2), Some(x2)) => Some(Comb(f2, x2))
        _ => None
      }
    Abs(bv, body) =>
      if alpha_eq(bv, v) {
        Some(t)
      } else {
        let capture_risk = vfree_in(bv, repl) && vfree_in(v, body)
        if capture_risk {
          None
        } else {
          match subst_var_safe(v, repl, body) {
            Some(body2) => Some(Abs(bv, body2))
            None => None
          }
        }
      }
  }
}

///|
pub fn trans(th1 : Thm, th2 : Thm) -> Thm? {
  match th1 {
    Sequent(h1, c1) =>
      match th2 {
        Sequent(h2, c2) =>
          match (dest_eq(c1), dest_eq(c2)) {
            (Some((l1, r1)), Some((l2, r2))) =>
              if alpha_eq(r1, l2) {
                Some(Sequent(hyps_union(h1, h2), mk_eq(l1, r2)))
              } else {
                None
              }
            _ => None
          }
      }
  }
}

///|
pub fn abs_rule(x : Term, th : Thm) -> Thm? {
  if !is_var(x) {
    return None
  }
  match th {
    Sequent(hs, concl) =>
      if vfree_in_hyps(x, hs) {
        None
      } else {
        match dest_eq(concl) {
          Some((l, r)) => Some(Sequent(hs, mk_eq(mk_abs(x, l), mk_abs(x, r))))
          _ => None
        }
      }
  }
}

///|
pub fn beta_rule(t : Term) -> Thm? {
  match t {
    Comb(Abs(v, body), arg) =>
      if !is_var(v) || !ty_eq(type_of(v), type_of(arg)) {
        None
      } else {
        match subst_var_safe(v, arg, body) {
          Some(out) => Some(Sequent([], mk_eq(t, out)))
          None => None
        }
      }
    _ => None
  }
}

///|
pub fn eq_mp(th_eq : Thm, th_p : Thm) -> Thm? {
  match th_eq {
    Sequent(h_eq, c_eq) =>
      match th_p {
        Sequent(h_p, c_p) =>
          match dest_eq(c_eq) {
            Some((lhs, rhs)) => {
              let ok_l = is_bool_ty(type_of(lhs))
              let ok_r = is_bool_ty(type_of(rhs))
              let ok_m = alpha_eq(lhs, c_p)
              let ok = ok_l && ok_r && ok_m
              if ok {
                Some(Sequent(hyps_union(h_eq, h_p), rhs))
              } else {
                None
              }
            }
            _ => None
          }
      }
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
  match th {
    Sequent(hs, c) => {
      let hs2 = hyps_dedup(hs.map(fn(h) { apply_ty_subst_to_term(subst, h) }))
      let c2 = apply_ty_subst_to_term(subst, c)
      Some(Sequent(hs2, c2))
    }
  }
}

///|
pub fn inst(subst : Array[(Term, Term)], th : Thm) -> Thm? {
  if !is_valid_term_subst(subst) {
    return None
  }
  match th {
    Sequent(hs, c) => {
      let hs2 = hyps_dedup(hs.map(fn(h) { apply_term_subst_to_term(subst, h) }))
      let c2 = apply_term_subst_to_term(subst, c)
      Some(Sequent(hs2, c2))
    }
  }
}

///|
pub fn mk_comb_rule(th_fg : Thm, th_xy : Thm) -> Thm? {
  match th_fg {
    Sequent(hfg, cfg) =>
      match th_xy {
        Sequent(hxy, cxy) =>
          match (dest_eq(cfg), dest_eq(cxy)) {
            (Some((f, g)), Some((x, y))) =>
              match (dest_fun_ty(type_of(f)), dest_fun_ty(type_of(g))) {
                (Some((dom_f, cod_f)), Some((dom_g, cod_g))) => {
                  let ok_dom_f = ty_eq(dom_f, type_of(x))
                  let ok_dom_g = ty_eq(dom_g, type_of(y))
                  let ok_cod = ty_eq(cod_f, cod_g)
                  let ok = ok_dom_f && ok_dom_g && ok_cod
                  if ok {
                    Some(
                      Sequent(
                        hyps_union(hfg, hxy),
                        mk_eq(mk_comb(f, x), mk_comb(g, y)),
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
}

///|
pub fn kernel_thm_phase0_ready() -> Bool {
  true
}
