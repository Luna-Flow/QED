// Conformance tests derived from `inductive Derivation` in
// formal_verification/QEDFV/HOL/Derivation.lean.
//
// Each test is named `Derivation.<constructor>: ...` and checks the kernel
// rule against the Lean constructor: the conclusion and hypotheses must be the
// ones the constructor states, and each premise of the constructor must be
// enforced. Lean terms use de Bruijn indices, so syntactic equality there is
// alpha-equivalence here, and hypotheses are compared as sets because `Valid`
// only uses membership.

///|
fn[T, E] lc_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn lc_eq(lhs : Term, rhs : Term) -> Term {
  lc_ok(mk_eq(lhs, rhs))
}

///|
fn lc_concl_is(th : Thm, expected : Term) -> Bool {
  term_alpha_eq(lc_ok(thm_concl(th)), expected)
}

///|
/// Set equality of hypotheses modulo alpha-equivalence.
fn lc_hyps_are(th : Thm, expected : Array[Term]) -> Bool {
  let hyps = lc_ok(thm_hyps(th))
  hyps.all(h => expected.any(e => term_alpha_eq(h, e))) &&
  expected.all(e => hyps.any(h => term_alpha_eq(h, e)))
}

///|
test "Derivation.refl: concludes t = t with no hypotheses" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let f = mk_var("f", fun_ty(a, a))
  for t in [x, mk_comb(f, x), mk_abs(x, mk_comb(f, x))] {
    let th = lc_ok(refl_checked(st, t))
    assert_true(lc_concl_is(th, lc_eq(t, t)))
    assert_true(lc_hyps_are(th, []))
  }
}

///|
test "Derivation.refl: rejects ill-typed terms" {
  let st = empty_kernel_state()
  let x = mk_var("x", mk_tyvar("A"))
  let p = mk_var("p", bool_ty())
  assert_true(refl_checked(st, mk_comb(p, x)) is Err(_))
}

///|
test "Derivation.assume: concludes p from hypothesis p" {
  let st = empty_kernel_state()
  let p = mk_var("p", bool_ty())
  let th = lc_ok(assume_checked(st, p))
  assert_true(lc_concl_is(th, p))
  assert_true(lc_hyps_are(th, [p]))
}

///|
test "Derivation.assume: premise p : bool is enforced" {
  let st = empty_kernel_state()
  assert_true(
    assume_checked(st, mk_var("x", mk_tyvar("A"))) is Err(NotBoolTerm),
  )
}

///|
test "Derivation.addAssum: adds p to the hypotheses and keeps the conclusion" {
  let st = empty_kernel_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let th = lc_ok(add_assum_checked(st, p, lc_ok(assume_checked(st, q))))
  assert_true(lc_concl_is(th, q))
  assert_true(lc_hyps_are(th, [p, q]))
  // `p :: A.hyps` with p already in A.hyps is the same hypothesis set.
  let again = lc_ok(add_assum_checked(st, q, lc_ok(assume_checked(st, q))))
  assert_true(lc_hyps_are(again, [q]))
}

///|
test "Derivation.addAssum: premise p : bool is enforced" {
  let st = empty_kernel_state()
  let q = mk_var("q", bool_ty())
  let x = mk_var("x", mk_tyvar("A"))
  assert_true(
    add_assum_checked(st, x, lc_ok(assume_checked(st, q))) is Err(NotBoolTerm),
  )
}

///|
test "Derivation.trans: concludes x = z over the union of hypotheses" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let xy = lc_eq(x, y)
  let yz = lc_eq(y, z)
  let th = lc_ok(
    trans_checked(
      st,
      lc_ok(assume_checked(st, xy)),
      lc_ok(assume_checked(st, yz)),
    ),
  )
  assert_true(lc_concl_is(th, lc_eq(x, z)))
  assert_true(lc_hyps_are(th, [xy, yz]))
}

///|
test "Derivation.trans: middle terms are compared up to alpha" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let u = mk_var("u", a)
  let v = mk_var("v", a)
  let f = mk_var("f", fun_ty(a, a))
  let lu = mk_abs(u, u)
  let lv = mk_abs(v, v)
  let th1 = lc_ok(assume_checked(st, lc_eq(f, lu)))
  let th2 = lc_ok(refl_checked(st, lv))
  let th = lc_ok(trans_checked(st, th1, th2))
  assert_true(lc_concl_is(th, lc_eq(f, lv)))
}

///|
test "Derivation.trans: premises hA and hB are enforced" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let p = mk_var("p", bool_ty())
  let th_xy = lc_ok(assume_checked(st, lc_eq(x, y)))
  // B.concl must be `y = z` for the same y.
  let th_zx = lc_ok(assume_checked(st, lc_eq(z, x)))
  assert_true(trans_checked(st, th_xy, th_zx) is Err(AlphaMismatch))
  // Both conclusions must be equations.
  let th_p = lc_ok(assume_checked(st, p))
  assert_true(trans_checked(st, th_xy, th_p) is Err(NotAnEquality))
  assert_true(trans_checked(st, th_p, th_xy) is Err(NotAnEquality))
}

///|
test "Derivation.mkComb: concludes f x = g y over the union of hypotheses" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let f = mk_var("f", fun_ty(a, b))
  let g = mk_var("g", fun_ty(a, b))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let fg = lc_eq(f, g)
  let xy = lc_eq(x, y)
  let th = lc_ok(
    mk_comb_rule_checked(
      st,
      lc_ok(assume_checked(st, fg)),
      lc_ok(assume_checked(st, xy)),
    ),
  )
  assert_true(lc_concl_is(th, lc_eq(mk_comb(f, x), mk_comb(g, y))))
  assert_true(lc_hyps_are(th, [fg, xy]))
}

///|
test "Derivation.mkComb: f : a -> b and x : a are enforced" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let f = mk_var("f", fun_ty(a, b))
  let g = mk_var("g", fun_ty(a, b))
  let u = mk_var("u", b)
  let v = mk_var("v", b)
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th_fg = lc_ok(assume_checked(st, lc_eq(f, g)))
  let th_uv = lc_ok(assume_checked(st, lc_eq(u, v)))
  let th_xy = lc_ok(assume_checked(st, lc_eq(x, y)))
  // Argument type differs from the domain.
  assert_true(mk_comb_rule_checked(st, th_fg, th_uv) is Err(TypeMismatch))
  // Left equation is not between functions.
  assert_true(mk_comb_rule_checked(st, th_xy, th_xy) is Err(TypeMismatch))
}

///|
test "Derivation.abs: concludes (λx. s) = (λx. t) with the same hypotheses" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let f = mk_var("f", fun_ty(a, a))
  let s = mk_comb(f, x)
  let hyp = lc_eq(f, mk_abs(y, y))
  let premise = lc_ok(
    mk_comb_rule_checked(
      st,
      lc_ok(assume_checked(st, hyp)),
      lc_ok(refl_checked(st, x)),
    ),
  )
  let th = lc_ok(abs_rule_checked(st, x, premise))
  let t = mk_comb(mk_abs(y, y), x)
  assert_true(lc_concl_is(th, lc_eq(mk_abs(x, s), mk_abs(x, t))))
  assert_true(lc_hyps_are(th, [hyp]))
}

///|
test "Derivation.abs: the binder must not be free in the hypotheses" {
  // In Lean the premise hypotheses are `weakenSequent A`, which cannot mention
  // the new de Bruijn variable.
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th = lc_ok(assume_checked(st, lc_eq(x, y)))
  assert_true(abs_rule_checked(st, x, th) is Err(VarFreeInHyp))
  // A variable with the same name but a different type is a different
  // variable, so x : bool may be abstracted and the free x : A stays free.
  let x_bool = mk_var("x", bool_ty())
  let z_bool = mk_var("z", bool_ty())
  let th_ok = lc_ok(abs_rule_checked(st, x_bool, th))
  assert_true(lc_concl_is(th_ok, lc_eq(mk_abs(z_bool, x), mk_abs(z_bool, y))))
  assert_true(lc_hyps_are(th_ok, [lc_eq(x, y)]))
}

///|
test "Derivation.abs: only a variable can be abstracted" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let y = mk_var("y", a)
  let th = lc_ok(refl_checked(st, y))
  assert_true(abs_rule_checked(st, mk_const("c", a), th) is Err(_))
  assert_true(abs_rule_checked(st, lc_eq(y, y), th) is Err(_))
}

///|
test "Derivation.beta: concludes (λx. s) x' = s[x'/x]" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let f = mk_var("f", fun_ty(a, a))
  let body = mk_comb(f, mk_comb(f, x))
  let redex = mk_comb(mk_abs(x, body), x)
  let th = lc_ok(beta_rule_checked(st, redex))
  assert_true(lc_concl_is(th, lc_eq(redex, body)))
  assert_true(lc_hyps_are(th, []))
}

///|
test "Derivation.beta: substitution avoids capturing free variables of the argument" {
  // `Sub.single` shifts the argument under binders, so a free y in the
  // argument stays free: (λx. λy. x) y = λz. y, never λy. y.
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let redex = mk_comb(mk_abs(x, mk_abs(y, x)), y)
  match beta_rule_checked(st, redex) {
    Ok(th) => {
      assert_true(lc_concl_is(th, lc_eq(redex, mk_abs(z, y))))
      assert_false(lc_concl_is(th, lc_eq(redex, mk_abs(y, y))))
    }
    // The kernel may restrict BETA to `(λx. s) x`; it must not capture.
    Err(e) => assert_true(e is NotTrivialBetaRedex)
  }
}

///|
test "Derivation.beta: the argument type must match the binder" {
  let st = empty_kernel_state()
  let x = mk_var("x", mk_tyvar("A"))
  let z = mk_var("z", mk_tyvar("B"))
  assert_true(
    beta_rule_checked(st, mk_comb(mk_abs(x, x), z)) is Err(TypeMismatch),
  )
  assert_true(beta_rule_checked(st, x) is Err(NotTrivialBetaRedex))
}

///|
test "Derivation.eqMp: concludes q over the union of hypotheses" {
  let st = empty_kernel_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let r = mk_var("r", bool_ty())
  let pq = lc_eq(p, q)
  let th_p = lc_ok(add_assum_checked(st, r, lc_ok(assume_checked(st, p))))
  let th = lc_ok(eq_mp_checked(st, lc_ok(assume_checked(st, pq)), th_p))
  assert_true(lc_concl_is(th, q))
  assert_true(lc_hyps_are(th, [pq, p, r]))
}

///|
test "Derivation.eqMp: B.concl is compared with p up to alpha" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let u = mk_var("u", a)
  let v = mk_var("v", a)
  let q = mk_var("q", bool_ty())
  let p_u = lc_eq(mk_abs(u, u), mk_abs(u, u))
  let p_v = lc_eq(mk_abs(v, v), mk_abs(v, v))
  let th_eq = lc_ok(assume_checked(st, lc_eq(p_u, q)))
  let th = lc_ok(eq_mp_checked(st, th_eq, lc_ok(assume_checked(st, p_v))))
  assert_true(lc_concl_is(th, q))
}

///|
test "Derivation.eqMp: premises hA and hB are enforced" {
  let st = empty_kernel_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let r = mk_var("r", bool_ty())
  let th_pq = lc_ok(assume_checked(st, lc_eq(p, q)))
  let th_r = lc_ok(assume_checked(st, r))
  assert_true(eq_mp_checked(st, th_pq, th_r) is Err(AlphaMismatch))
  assert_true(eq_mp_checked(st, th_r, th_r) is Err(NotAnEquality))
}

///|
test "Derivation.deduct: removes each conclusion from the other hypotheses" {
  let st = empty_kernel_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let r = mk_var("r", bool_ty())
  // A = {q, r} ⊢ p and B = {p} ⊢ q.
  let th_a = lc_ok(
    add_assum_checked(
      st,
      r,
      lc_ok(add_assum_checked(st, q, lc_ok(assume_checked(st, p)))),
    ),
  )
  let th_a = lc_ok(eq_mp_checked(st, lc_ok(refl_checked(st, p)), th_a))
  let th_b = lc_ok(add_assum_checked(st, p, lc_ok(assume_checked(st, q))))
  let th = lc_ok(deduct_antisym_rule_checked(st, th_a, th_b))
  assert_true(lc_concl_is(th, lc_eq(p, q)))
  // remove {p, q, r} q ∪ remove {p, q} p = {p, r} ∪ {q}.
  assert_true(lc_hyps_are(th, [p, r, q]))
}

///|
test "Derivation.deduct: removal is up to alpha and keeps unrelated hypotheses" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let u = mk_var("u", a)
  let v = mk_var("v", a)
  let r = mk_var("r", bool_ty())
  let p_u = lc_eq(mk_abs(u, u), mk_abs(u, u))
  let p_v = lc_eq(mk_abs(v, v), mk_abs(v, v))
  // A = {p_v, r} ⊢ p_v and B = ∅ ⊢ p_u.
  let th_a = lc_ok(add_assum_checked(st, r, lc_ok(assume_checked(st, p_v))))
  let th_b = lc_ok(refl_checked(st, mk_abs(u, u)))
  let th = lc_ok(deduct_antisym_rule_checked(st, th_a, th_b))
  assert_true(lc_concl_is(th, lc_eq(p_v, p_u)))
  assert_true(lc_hyps_are(th, [r]))
}

///|
test "Derivation.instType: instantiates every hypothesis and the conclusion" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let hyp = lc_eq(x, y)
  let th = lc_ok(
    trans_checked(
      st,
      lc_ok(assume_checked(st, hyp)),
      lc_ok(refl_checked(st, y)),
    ),
  )
  let out = lc_ok(inst_type(st, [("A", b)], th))
  let xb = mk_var("x", b)
  let yb = mk_var("y", b)
  assert_true(lc_concl_is(out, lc_eq(xb, yb)))
  assert_true(lc_hyps_are(out, [lc_eq(xb, yb)]))
}

///|
test "Derivation.instType: the substitution is simultaneous" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let f = mk_var("f", fun_ty(a, b))
  let out = lc_ok(
    inst_type(st, [("A", b), ("B", a)], lc_ok(refl_checked(st, f))),
  )
  let g = mk_var("f", fun_ty(b, a))
  assert_true(lc_concl_is(out, lc_eq(g, g)))
}

///|
test "Derivation.instType: binder structure is preserved when types collapse" {
  // Lean instantiates the type of each de Bruijn position, so a bound y : A
  // and a free x : B stay distinct when A and B both become bool.
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let lam = mk_abs(mk_var("y", a), mk_var("x", b))
  let out = lc_ok(
    inst_type(
      st,
      [("A", bool_ty()), ("B", bool_ty())],
      lc_ok(refl_checked(st, lam)),
    ),
  )
  let x = mk_var("x", bool_ty())
  let expected = mk_abs(mk_var("z", bool_ty()), x)
  assert_true(lc_concl_is(out, lc_eq(expected, expected)))
  assert_false(lc_concl_is(out, lc_eq(mk_abs(x, x), mk_abs(x, x))))
}

///|
test "Derivation.refl: named results never capture free variables" {
  // Conclusions are stored with de Bruijn indices and given names only at the
  // public boundary; a free variable that looks like a generated binder name
  // must stay free.
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  for name in ["_b0", "_b1"] {
    let free = mk_var(name, a)
    let lam = mk_abs(mk_var("y", a), mk_abs(mk_var("w", a), free))
    let th = lc_ok(refl_checked(st, lam))
    assert_true(lc_concl_is(th, lc_eq(lam, lam)))
    let shown = lc_ok(thm_concl(th))
    assert_true(free_vars(shown).any(v => v.0 == name))
  }
}

///|
test "Derivation.instType: duplicate keys are rejected" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let th = lc_ok(refl_checked(st, mk_var("x", a)))
  assert_true(
    inst_type(st, [("A", bool_ty()), ("A", ind_ty())], th)
    is Err(InvalidInstantiation),
  )
}

///|
test "Derivation.instTerm: substitutes every hypothesis and the conclusion" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let f = mk_var("f", fun_ty(a, a))
  let fx = mk_comb(f, x)
  let hyp = lc_eq(x, y)
  let th = lc_ok(
    trans_checked(
      st,
      lc_ok(assume_checked(st, hyp)),
      lc_ok(refl_checked(st, y)),
    ),
  )
  let out = lc_ok(inst_checked(st, [(x, fx)], th))
  assert_true(lc_concl_is(out, lc_eq(fx, y)))
  assert_true(lc_hyps_are(out, [lc_eq(fx, y)]))
}

///|
test "Derivation.instTerm: the substitution is simultaneous" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th = lc_ok(assume_checked(st, lc_eq(x, y)))
  let out = lc_ok(inst_checked(st, [(x, y), (y, x)], th))
  assert_true(lc_concl_is(out, lc_eq(y, x)))
  assert_true(lc_hyps_are(out, [lc_eq(y, x)]))
}

///|
test "Derivation.instTerm: substitution avoids capture under binders" {
  // `Term.substitute` lifts σ under a binder, so a substituted free x stays
  // free: (λx. y)[x/y] = λz. x.
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let lam = mk_abs(x, y)
  let out = lc_ok(inst_checked(st, [(y, x)], lc_ok(refl_checked(st, lam))))
  let expected = mk_abs(z, x)
  assert_true(lc_concl_is(out, lc_eq(expected, expected)))
  assert_false(lc_concl_is(out, lc_eq(mk_abs(x, x), mk_abs(x, x))))
}

///|
test "Derivation.instTerm: bound occurrences are not substituted" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let lam = mk_abs(x, x)
  let out = lc_ok(inst_checked(st, [(x, y)], lc_ok(refl_checked(st, lam))))
  assert_true(lc_concl_is(out, lc_eq(lam, lam)))
}

///|
test "Derivation.instTerm: σ must be a well-typed map from variables" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let p = mk_var("p", bool_ty())
  let th = lc_ok(refl_checked(st, x))
  // Value type differs from the variable type.
  assert_true(inst_checked(st, [(x, p)], th) is Err(_))
  // Keys must be variables.
  assert_true(inst_checked(st, [(lc_eq(x, x), p)], th) is Err(_))
  // A variable may be mapped only once.
  assert_true(inst_checked(st, [(x, x), (x, mk_var("y", a))], th) is Err(_))
}
