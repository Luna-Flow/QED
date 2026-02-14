///|
fn[T, E] expect_ok_logic(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "logic wrappers call kernel rules" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let st = expect_ok_logic(@kernel.ks_add_const(st0, "P", bool))
  let p = expect_ok_logic(@kernel.ks_mk_const(st, "P"))
  let th_assume = logic_assume(st, p)
  assert_true(th_assume is Ok(_))

  let x = @kernel.mk_var("x", @kernel.mk_tyvar("A"))
  let th_refl = logic_refl(st, x)
  assert_true(th_refl is Ok(_))
}

///|
test "logic checked wrappers reject inadmissible constants and id drift" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let p = @kernel.mk_const("P", bool)
  assert_true(logic_assume(st0, p) is Err(@kernel.TypeMismatch))

  let st1 = expect_ok_logic(@kernel.ks_add_const(st0, "P", bool))
  let p1 = expect_ok_logic(@kernel.ks_mk_const(st1, "P"))
  assert_true(logic_assume(st1, p1) is Ok(_))

  let th_refl = expect_ok_logic(logic_refl(st1, p1))
  let st2 = @kernel.ks_push_scope(st1)
  let st3 = expect_ok_logic(@kernel.ks_add_const(st2, "P", bool))
  assert_true(
    logic_trans(st3, th_refl, th_refl) is Err(@kernel.InvalidInstantiation),
  )

  let p3 = expect_ok_logic(@kernel.ks_mk_const(st3, "P"))
  let drifted_refl = expect_ok_logic(logic_refl(st3, p3))
  assert_true(
    logic_trans(st1, drifted_refl, drifted_refl)
    is Err(@kernel.InvalidInstantiation),
  )
}

///|
test "logic trans wrapper composes equality theorems" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let z = @kernel.mk_var("z", a)

  let th1 = expect_ok_logic(
    logic_assume(st, expect_ok_logic(@kernel.mk_eq(x, y))),
  )
  let th2 = expect_ok_logic(
    logic_assume(st, expect_ok_logic(@kernel.mk_eq(y, z))),
  )
  assert_true(logic_trans(st, th1, th2) is Ok(_))
}
