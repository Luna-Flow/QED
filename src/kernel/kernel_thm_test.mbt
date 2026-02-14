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
fn type_witness_bundle_for_inst() -> (Term, Thm) {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let id = mk_abs(x, x)
  let pred = expect_ok(mk_eq(id, id))
  let witness = expect_ok(refl(id))
  (pred, witness)
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
test "checked theorem wrappers enforce state admissibility" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let u = mk_const("U", bool)
  assert_true(assume_checked(st0, u) is Err(TypeMismatch))
  assert_true(refl_checked(st0, u) is Err(TypeMismatch))

  let st1 = expect_ok_sig_for_thm(ks_add_const(st0, "U", bool))
  let th_u = expect_ok(assume_checked(st1, u))
  assert_true(thm_is_admissible(st1, th_u))
  assert_true(assume_checked(st1, u) is Ok(_))
  assert_true(inst_checked(st1, [], th_u) is Ok(_))
}

///|
test "checked trans rejects inadmissible input theorem" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let u = mk_const("U", bool)
  let bad_th = expect_ok(assume(u))
  assert_true(trans_checked(st0, bad_th, bad_th) is Err(TypeMismatch))

  let st1 = expect_ok_sig_for_thm(ks_add_const(st0, "U", bool))
  assert_true(trans_checked(st1, bad_th, bad_th) is Err(InvalidInstantiation))
}

///|
test "checked theorems reject const id drift under shadowing" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_sig_for_thm(ks_add_const(st0, "c", bool))
  let th = expect_ok(assume_checked(st1, mk_const("c", bool)))
  assert_true(thm_is_admissible(st1, th))

  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig_for_thm(ks_add_const(st2, "c", bool))
  assert_false(thm_is_admissible(st3, th))
  assert_true(inst_checked(st3, [], th) is Err(InvalidInstantiation))
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
test "rules reject malformed named binder typing at boundary" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x_a = mk_var("x", a)
  let x_b = mk_var("x", b)
  let bad = mk_abs(x_a, x_b)
  assert_true(refl(bad) is Err(BoundaryFailure))
}

///|
test "dest_eq rejects malformed equality constant instances" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", b)
  let bad_eq_ty = fun_ty(a, fun_ty(b, bool_ty()))
  let bad_eq = mk_comb(mk_comb(mk_const("=", bad_eq_ty), x), y)
  assert_true(dest_eq(bad_eq) is Err(TypeMismatch))
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

  let b = mk_tyvar("B")
  let u = mk_var("u", b)
  let bad_eq_ty = fun_ty(a, fun_ty(b, bool_ty()))
  let bad_mid = mk_comb(mk_comb(mk_const("=", bad_eq_ty), y), u)
  let th_bad_eq = expect_ok(assume(bad_mid))
  assert_true(trans(th1, th_bad_eq) is Err(TypeMismatch))
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

  let (pred, witness) = type_witness_bundle_for_inst()
  let st1 = expect_ok_sig_for_thm(
    ks_register_type_definition(st0, "custom", 1, "RepCustom", pred, witness),
  )
  assert_true(inst_type(st1, [("A", custom)], th) is Ok(_))
}

///|
test "inst_type enforces constant schema instances" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()

  let st1 = expect_ok_sig_for_thm(ks_add_const(st0, "id", fun_ty(a, a)))
  let th_ok = expect_ok(refl_checked(st1, mk_const("id", fun_ty(a, a))))
  assert_true(inst_type(st1, [("A", bool)], th_ok) is Ok(_))

  let th_bad = expect_ok(refl(mk_const("id", fun_ty(bool, a))))
  assert_true(inst_type(st1, [], th_bad) is Err(InvalidInstantiation))

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
