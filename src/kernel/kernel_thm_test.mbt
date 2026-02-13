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
test "thm trans accepts alpha-equivalent middle term" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", b)

  let id_x = mk_abs(x, x)
  let id_y = mk_abs(y, y)
  let k = mk_abs(x, z)

  let th1 = assume(mk_eq(k, id_x))
  let th2 = assume(mk_eq(id_y, k))
  assert_true((th1, th2) is (Some(_), Some(_)))

  match (th1, th2) {
    (Some(t1), Some(t2)) => {
      let out = trans(t1, t2)
      assert_true(out is Some(_))
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

///|
test "thm mk_comb_rule fails on non-equality premise" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let fty = fun_ty(a, b)
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let p = mk_const("P", bool_ty())
  let f = mk_const("f", fty)
  let g = mk_const("g", fty)

  let th_bad = assume(p)
  let th_xy = assume(mk_eq(x, y))
  let th_fg = assume(mk_eq(f, g))
  assert_true((th_bad, th_xy, th_fg) is (Some(_), Some(_), Some(_)))

  match (th_bad, th_xy, th_fg) {
    (Some(tb), Some(txy), Some(tfg)) => {
      assert_true(mk_comb_rule(tb, txy) is None)
      assert_true(mk_comb_rule(tfg, tb) is None)
    }
    _ => assert_false(true)
  }
}

///|
test "thm abs_rule abstracts equality theorem" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let th = assume(mk_eq(y, z))
  assert_true(th is Some(_))
  match th {
    Some(t) => {
      let out = abs_rule(x, t)
      assert_true(out is Some(Sequent(_, _)))
    }
    None => assert_false(true)
  }
}

///|
test "thm abs_rule fails when binder free in assumptions" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th = assume(mk_eq(x, y))
  assert_true(th is Some(_))
  match th {
    Some(t) => {
      let out = abs_rule(x, t)
      assert_true(out is None)
    }
    None => assert_false(true)
  }
}

///|
test "thm abs_rule fails for non-variable binder" {
  let a = mk_tyvar("A")
  let c = mk_const("c", a)
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th = assume(mk_eq(x, y))
  assert_true(th is Some(_))
  match th {
    Some(t) => assert_true(abs_rule(c, t) is None)
    None => assert_false(true)
  }
}

///|
test "thm beta_rule succeeds on trivial beta redex" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let redex = mk_comb(mk_abs(x, y), x)
  let out = beta_rule(redex)
  assert_true(out is Some(Sequent(_, _)))
}

///|
test "thm beta_rule rejects nontrivial redex" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let redex = mk_comb(mk_abs(x, y), z)
  let out = beta_rule(redex)
  assert_true(out is None)
}

///|
test "thm eq_mp derives rhs from equality and lhs proof" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let th_eq = assume(mk_eq(p, q))
  let th_p = assume(p)
  assert_true((th_eq, th_p) is (Some(_), Some(_)))

  match (th_eq, th_p) {
    (Some(teq), Some(tp)) => {
      let out = eq_mp(teq, tp)
      assert_true(out is Some(Sequent(_, _)))
    }
    _ => assert_false(true)
  }
}

///|
test "thm eq_mp fails when lhs does not match premise" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let r = mk_const("R", bool_ty())
  let th_eq = assume(mk_eq(p, q))
  let th_r = assume(r)
  assert_true((th_eq, th_r) is (Some(_), Some(_)))

  match (th_eq, th_r) {
    (Some(teq), Some(tr)) => {
      let out = eq_mp(teq, tr)
      assert_true(out is None)
    }
    _ => assert_false(true)
  }
}

///|
test "thm deduct_antisym_rule builds equality theorem" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let th_p = assume(p)
  let th_q = assume(q)
  assert_true((th_p, th_q) is (Some(_), Some(_)))

  match (th_p, th_q) {
    (Some(tp), Some(tq)) => {
      let out = deduct_antisym_rule(tp, tq)
      assert_true(out is Sequent(_, Comb(Comb(Const("=", _), _), _)))
    }
    _ => assert_false(true)
  }
}

///|
test "thm deduct_antisym_rule removes opposite assumptions" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let th_p = assume(p)
  let th_q = assume(q)
  assert_true((th_p, th_q) is (Some(_), Some(_)))

  match (th_p, th_q) {
    (Some(tp), Some(tq)) =>
      match deduct_antisym_rule(tp, tq) {
        Sequent(hs, _) => assert_eq(hs.length(), 2)
      }
    _ => assert_false(true)
  }
}

///|
test "thm inst_type accepts empty substitution" {
  let p = mk_const("P", bool_ty())
  let th = assume(p)
  assert_true(th is Some(_))
  match th {
    Some(t) => {
      let out = inst_type([], t)
      assert_true(out is Some(_))
    }
    None => assert_false(true)
  }
}

///|
test "thm inst_type applies non-empty substitution" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th = refl(x)
  let out = inst_type([("A", bool_ty())], th)
  assert_true(out is Some(_))
  match out {
    Some(Sequent(_, concl)) =>
      match concl {
        Comb(Comb(Const("=", _), lhs), _) =>
          assert_true(type_of(lhs) is TyApp("bool", []))
        _ => assert_false(true)
      }
    None => assert_false(true)
  }
}

///|
test "thm inst accepts empty substitution" {
  let p = mk_const("P", bool_ty())
  let th = assume(p)
  assert_true(th is Some(_))
  match th {
    Some(t) => {
      let out = inst([], t)
      assert_true(out is Some(_))
    }
    None => assert_false(true)
  }
}

///|
test "thm inst applies non-empty substitution" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let th = refl(x)
  let out = inst([(x, y)], th)
  assert_true(out is Some(_))
  match out {
    Some(Sequent(_, concl)) =>
      assert_true(term_to_string(concl).contains("Var(y : A)"))
    None => assert_false(true)
  }
}

///|
test "thm inst rejects invalid substitution key" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("C", a)
  let out = inst([(c, x)], refl(x))
  assert_true(out is None)
}

///|
test "thm inst blocks substitution that would capture binder" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let lam = mk_abs(y, x)
  let th = refl(lam)
  let out = inst([(x, y)], th)
  assert_true(out is Some(_))

  match out {
    Some(Sequent(_, concl)) => {
      let s = term_to_string(concl)
      assert_true(s.contains("Abs(Var(y : A), Var(x : A))"))
    }
    None => assert_false(true)
  }
}
