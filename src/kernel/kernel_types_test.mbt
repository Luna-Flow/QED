///|
test "types constructors" {
  let a = mk_tyvar("A")
  assert_true(is_tyvar(a))

  let bool = bool_ty()
  assert_true(is_tyapp(bool))

  let fun = fun_ty(a, bool)
  assert_true(is_tyapp(fun))
}

///|
test "types shape pattern" {
  let a = mk_tyvar("A")
  assert_true(a is TyVal(_))

  let bool = bool_ty()
  assert_true(bool is TyApp("bool", _))

  let fun = fun_ty(a, bool)
  assert_true(fun is TyApp("fun", _))
}
