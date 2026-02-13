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

///|
test "terms comb constructor" {
  let bool = bool_ty()
  let f_ty = fun_ty(bool, bool)
  let f = mk_const("f", f_ty)
  let x = mk_var("x", bool)
  let app = mk_comb(f, x)
  assert_true(app is Comb(_, _))
}

///|
test "terms comb type_of" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let f = mk_const("f", fun_ty(a, b))
  let x = mk_var("x", a)
  let app = mk_comb(f, x)
  assert_true(type_of(app) is TyVal("B"))
}

///|
test "terms abs constructor" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let body = mk_var("y", a)
  let lam = mk_abs(x, body)
  assert_true(lam is Abs(_, _))
}

///|
test "terms abs type_of" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let k = mk_const("k", b)
  let lam = mk_abs(x, k)
  assert_true(type_of(lam) is TyApp("fun", [TyVal("A"), TyVal("B")]))
}
