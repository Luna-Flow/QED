///|
test "thm refl builds equality theorem" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th = refl(x)

  assert_true(th is Sequent([], _))

  match th {
    Sequent(_, concl) => assert_true(concl is Comb(Comb(Const("=", _), _), _))
  }
}

///|
test "thm assume accepts bool proposition" {
  let p = mk_const("P", bool_ty())
  let th = assume(p)
  assert_true(th is Some(Sequent(_, _)))

  match th {
    Some(Sequent(hyps, concl)) => {
      assert_eq(hyps.length(), 1)
      assert_true(concl is Const("P", _))
    }
    None => assert_false(true)
  }
}

///|
test "thm assume rejects non-bool term" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th = assume(x)
  assert_true(th is None)
}

///|
test "thm trans combines equalities" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let eq1 = mk_eq(x, y)
  let eq2 = mk_eq(y, z)

  let th1 = Some(assume(eq1))
  let th2 = Some(assume(eq2))
  assert_true((th1, th2) is (Some(Some(_)), Some(Some(_))))

  match (th1, th2) {
    (Some(Some(t1)), Some(Some(t2))) => {
      let out = trans(t1, t2)
      assert_true(out is Some(Sequent(_, _)))
    }
    _ => assert_false(true)
  }
}

///|
test "thm trans fails on mismatch middle term" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let th1 = assume(mk_eq(x, y))
  let th2 = assume(mk_eq(z, x))
  assert_true((th1, th2) is (Some(_), Some(_)))

  match (th1, th2) {
    (Some(t1), Some(t2)) => {
      let out = trans(t1, t2)
      assert_true(out is None)
    }
    _ => assert_false(true)
  }
}

///|
test "thm mk_comb_rule combines function and argument equalities" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let fty = fun_ty(a, b)
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let f = mk_const("f", fty)
  let g = mk_const("g", fty)

  let th_fg = assume(mk_eq(f, g))
  let th_xy = assume(mk_eq(x, y))
  assert_true((th_fg, th_xy) is (Some(_), Some(_)))

  match (th_fg, th_xy) {
    (Some(tfg), Some(txy)) => {
      let out = mk_comb_rule(tfg, txy)
      assert_true(out is Some(Sequent(_, _)))
    }
    _ => assert_false(true)
  }
}

///|
test "thm mk_comb_rule fails on argument type mismatch" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let c = mk_tyvar("C")
  let fty = fun_ty(a, b)
  let x = mk_var("x", c)
  let y = mk_var("y", c)
  let f = mk_const("f", fty)
  let g = mk_const("g", fty)

  let th_fg = assume(mk_eq(f, g))
  let th_xy = assume(mk_eq(x, y))
  assert_true((th_fg, th_xy) is (Some(_), Some(_)))

  match (th_fg, th_xy) {
    (Some(tfg), Some(txy)) => {
      let out = mk_comb_rule(tfg, txy)
      assert_true(out is None)
    }
    _ => assert_false(true)
  }
}
