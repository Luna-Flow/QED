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
