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
  let p = @kernel.mk_const("P", bool)
  let th_assume = logic_assume(st, p)
  assert_true(th_assume is Ok(_))

  let x = @kernel.mk_var("x", @kernel.mk_tyvar("A"))
  let th_refl = logic_refl(st, x)
  assert_true(th_refl is Ok(_))
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
