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

///|
test "types pretty printer" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let fn_ty = fun_ty(a, b)
  let rendered = hol_type_to_string(fn_ty)
  assert_eq(rendered, "fun(A, B)")
}

///|
test "types substitution and duplicate key rejection" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let ty = fun_ty(a, a)

  assert_true(
    type_subst([("A", b)], ty) is Some(TyApp("fun", [TyVal("B"), TyVal("B")])),
  )
  assert_true(type_subst([("A", b), ("A", a)], ty) is None)
}

///|
test "types tyvars and subset relation" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let c = mk_tyvar("C")

  let lhs = fun_ty(a, b)
  let rhs = fun_ty(fun_ty(a, b), c)
  assert_true(tyvars_subset(lhs, rhs))
  assert_false(tyvars_subset(rhs, lhs))
}

///|
test "types instance relation checks schema matching" {
  let a = mk_tyvar("A")
  let schema = fun_ty(a, a)
  let inst1 = fun_ty(bool_ty(), bool_ty())
  let inst2 = fun_ty(bool_ty(), mk_tyvar("B"))
  assert_true(ty_is_instance_of(inst1, schema))
  assert_false(ty_is_instance_of(inst2, schema))
}
