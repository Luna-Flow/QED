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
