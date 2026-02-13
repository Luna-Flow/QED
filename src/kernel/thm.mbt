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
pub fn kernel_thm_phase0_ready() -> Bool {
  true
}
