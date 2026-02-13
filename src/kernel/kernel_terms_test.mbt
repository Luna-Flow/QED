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

///|
test "terms predicates" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, c)

  assert_true(is_var(x))
  assert_false(is_var(c))

  assert_true(is_const(c))
  assert_false(is_const(app))

  assert_true(is_comb(app))
  assert_false(is_comb(lam))

  assert_true(is_abs(lam))
  assert_false(is_abs(x))
}

///|
test "terms destructors" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, c)

  assert_true(dest_var(x) is Some(("x", _)))
  assert_true(dest_var(c) is None)

  assert_true(dest_const(c) is Some(("c", _)))
  assert_true(dest_const(x) is None)

  assert_true(dest_comb(app) is Some((_, _)))
  assert_true(dest_comb(lam) is None)

  assert_true(dest_abs(lam) is Some((_, _)))
  assert_true(dest_abs(app) is None)
}

///|
test "terms pretty printer" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, app)

  let rendered = term_to_string(lam)
  assert_true(rendered.contains("Abs("))
  assert_true(rendered.contains("Comb("))
  assert_true(rendered.contains("Var(x : A)"))
}

///|
test "terms debruijn string keeps alpha shape" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)

  let t1 = mk_abs(x, x)
  let t2 = mk_abs(y, y)

  assert_eq(db_string(t1), db_string(t2))
  assert_true(db_string(t1).contains("BVar(0 : A)"))
}
