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

///|
test "types destructors" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let fn_ty = fun_ty(a, b)

  let tyapp = dest_tyapp(fn_ty)
  assert_true(tyapp is Some(_))

  let de_fun = dest_fun_ty(fn_ty)
  assert_true(de_fun is Some((_, _)))

  let non_fun = dest_fun_ty(bool_ty())
  assert_true(non_fun is None)
}

///|
test "types bool predicate" {
  assert_true(is_bool_ty(bool_ty()))

  let a = mk_tyvar("A")
  assert_false(is_bool_ty(a))
}
