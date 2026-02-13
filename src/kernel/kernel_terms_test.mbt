///|
test "terms constructors" {
  let bool = bool_ty()

  let v = mk_var("x", bool)
  assert_true(v is Var("x", _))

  let c = mk_const("T", bool)
  assert_true(c is Const("T", _))
}

///|
test "terms type_of" {
  let a = mk_tyvar("A")

  let v = mk_var("x", a)
  assert_true(type_of(v) is TyVal("A"))

  let c = mk_const("k", bool_ty())
  assert_true(type_of(c) is TyApp("bool", []))
}
