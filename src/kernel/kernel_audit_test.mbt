///|
fn[T, E] expect_ok_audit(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn[T] expect_ok_sig_audit(res : Result[T, SigError]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "audit c5 pop then redefine stays rejected by defheads" {
  let st0 = empty_kernel_state()
  let p = mk_const("P", bool_ty())
  let (st1, _) = expect_ok_sig_audit(ks_define_const(st0, "q", bool_ty(), p))
  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig_audit(ks_pop_scope(st2))
  assert_true(
    ks_define_const(st3, "q", bool_ty(), p) is Err(DefinitionAlreadyExists),
  )
}

///|
test "audit d1 typedef rejects non theorem witness" {
  let st0 = empty_kernel_state()
  let bad_w = expect_ok_audit(assume(mk_const("P", bool_ty())))
  assert_true(
    ks_register_type_definition(st0, "newty", 1, bad_w)
    is Err(InvalidTypeWitness),
  )
}

///|
test "audit d5 polymorphic constant instantiation guard" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st1 = expect_ok_sig_audit(ks_add_const(st0, "id", fun_ty(a, a)))
  let th = expect_ok_audit(refl(mk_const("id", fun_ty(a, a))))
  assert_true(inst_type(st1, [("A", bool)], th) is Ok(_))
  let bad = expect_ok_audit(refl(mk_const("id", fun_ty(bool, a))))
  assert_true(inst_type(st1, [], bad) is Err(TypeMismatch))
}

///|
test "audit e2 trans rejects typed middle mismatch" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let k = mk_var("k", fun_ty(a, a))
  let id_ok = mk_abs(x, x)
  let id_bad = mk_abs(x, y)

  let th1 = expect_ok_audit(assume(expect_ok_audit(mk_eq(k, id_ok))))
  let th2 = expect_ok_audit(assume(expect_ok_audit(mk_eq(id_bad, k))))
  assert_true(trans(th1, th2) is Err(AlphaMismatch))
}

///|
test "audit e3 beta binder agreement check" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", b)
  let redex = mk_comb(mk_abs(x, x), y)
  assert_true(beta_rule(redex) is Err(TypeMismatch))
}
