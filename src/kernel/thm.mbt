///|
/// Theorem object and primitive rule placeholders for kernel phase 1.
pub enum Thm {
  Sequent(Array[Term], Term)
}

///|
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
  term_to_string(t1) == term_to_string(t2)
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
