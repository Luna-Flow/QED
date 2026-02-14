///|
fn[T, E] expect_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn[T] expect_ok_sig_for_thm(res : Result[T, SigError]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "thm is opaque and observable through API" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th = expect_ok(refl(x))
  assert_eq(thm_hyp_count(th), 0)
  let concl = expect_ok(thm_concl(th))
  assert_true(dest_eq(concl) is Ok((_, _)))
}

///|
test "mk_eq enforces same type on both sides" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", b)
  assert_true(mk_eq(x, y) is Err(TypeMismatch))
}

///|
test "assume accepts only boolean propositions" {
  let p = mk_const("P", bool_ty())
  assert_true(assume(p) is Ok(_))
  let a = mk_tyvar("A")
  assert_true(assume(mk_var("x", a)) is Err(NotBoolTerm))
}

///|
test "trans composes equalities and checks alpha middle term" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let th1 = expect_ok(assume(expect_ok(mk_eq(x, y))))
  let th2 = expect_ok(assume(expect_ok(mk_eq(y, z))))
  let out = expect_ok(trans(th1, th2))
  assert_eq(thm_hyp_count(out), 2)

  let th_bad = expect_ok(assume(expect_ok(mk_eq(z, x))))
  assert_true(trans(th1, th_bad) is Err(AlphaMismatch))
}

///|
test "mk_comb_rule checks function typing constraints" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let c = mk_tyvar("C")
  let f = mk_const("f", fun_ty(a, b))
  let g = mk_const("g", fun_ty(a, b))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let u = mk_var("u", c)
  let v = mk_var("v", c)

  let th_fg = expect_ok(assume(expect_ok(mk_eq(f, g))))
  let th_xy = expect_ok(assume(expect_ok(mk_eq(x, y))))
  assert_true(mk_comb_rule(th_fg, th_xy) is Ok(_))

  let th_uv = expect_ok(assume(expect_ok(mk_eq(u, v))))
  assert_true(mk_comb_rule(th_fg, th_uv) is Err(TypeMismatch))
}

///|
test "abs_rule enforces binder and free-in-hyp side condition" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let th_eq = expect_ok(assume(expect_ok(mk_eq(y, z))))
  assert_true(abs_rule(x, th_eq) is Ok(_))

  let th_bad = expect_ok(assume(expect_ok(mk_eq(x, y))))
  assert_true(abs_rule(x, th_bad) is Err(VarFreeInHyp))

  let c = mk_const("c", a)
  assert_true(abs_rule(c, th_eq) is Err(InvalidInstantiation))
}

///|
test "beta_rule enforces redex shape and binder agreement" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", b)
  let redex = mk_comb(mk_abs(x, x), y)
  assert_true(beta_rule(redex) is Ok(_))

  let bad_ty = mk_comb(mk_abs(x, x), z)
  assert_true(beta_rule(bad_ty) is Err(TypeMismatch))

  assert_true(beta_rule(x) is Err(NotTrivialBetaRedex))
}

///|
test "eq_mp derives rhs and checks lhs matching" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let r = mk_const("R", bool_ty())
  let th_eq = expect_ok(assume(expect_ok(mk_eq(p, q))))
  let th_p = expect_ok(assume(p))
  assert_true(eq_mp(th_eq, th_p) is Ok(_))

  let th_r = expect_ok(assume(r))
  assert_true(eq_mp(th_eq, th_r) is Err(AlphaMismatch))
}

///|
test "deduct_antisym_rule removes opposite assumptions" {
  let p = mk_const("P", bool_ty())
  let q = mk_const("Q", bool_ty())
  let th_p = expect_ok(assume(p))
  let th_q = expect_ok(assume(q))
  let out = expect_ok(deduct_antisym_rule(th_p, th_q))
  assert_eq(thm_hyp_count(out), 2)
  let concl = expect_ok(thm_concl(out))
  assert_true(dest_eq(concl) is Ok((_, _)))
}

///|
test "inst_type validates substitution shape" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let th = expect_ok(refl(x))
  assert_true(inst_type(st, [("A", b)], th) is Ok(_))
  assert_true(
    inst_type(st, [("A", b), ("A", bool_ty())], th) is Err(InvalidInstantiation),
  )
}

///|
test "inst_type enforces admissible type targets" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th = expect_ok(refl(x))
  let custom = mk_tyapp("custom", [a])

  assert_true(inst_type(st0, [("A", custom)], th) is Err(InvalidInstantiation))

  let st1 = expect_ok_sig_for_thm(
    ks_register_type_definition(st0, "custom", 1, true),
  )
  assert_true(inst_type(st1, [("A", custom)], th) is Ok(_))
}

///|
test "inst_type enforces constant schema instances" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()

  let st1 = expect_ok_sig_for_thm(ks_add_const(st0, "id", fun_ty(a, a)))
  let th_ok = expect_ok(refl(mk_const("id", fun_ty(a, a))))
  assert_true(inst_type(st1, [("A", bool)], th_ok) is Ok(_))

  let th_bad = expect_ok(refl(mk_const("id", fun_ty(bool, a))))
  assert_true(inst_type(st1, [], th_bad) is Err(TypeMismatch))

  let th_unknown = expect_ok(refl(mk_const("u", bool)))
  assert_true(inst_type(st1, [], th_unknown) is Err(TypeMismatch))
}

///|
test "inst_type enforces definition instantiation coherence" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let id_ty = fun_ty(a, a)
  let rhs_id = mk_abs(mk_var("x", a), mk_var("x", a))
  let (st1, def_th) = expect_ok_sig_for_thm(
    ks_define_const_thm(st0, "id", id_ty, rhs_id),
  )
  assert_true(inst_type(st1, [("A", bool_ty())], def_th) is Ok(_))
  assert_true(inst_type(st1, [("A", mk_tyvar("B"))], def_th) is Ok(_))
}

///|
test "inst validates substitution map and types" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", b)
  let c = mk_const("C", a)
  let th = expect_ok(refl(x))

  assert_true(inst([(x, y)], th) is Ok(_))
  assert_true(inst([(c, y)], th) is Err(InvalidInstantiation))
  assert_true(inst([(x, z)], th) is Err(TypeMismatch))
}
