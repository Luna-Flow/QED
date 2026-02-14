///|
test "tactics goal construction" {
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_const("P", bool)
  let goal = mk_goal([p], p)
  assert_eq(goal_hyp_count(goal), 1)
  assert_true(goal_concl(goal) is @kernel.Const("P", _))
}

///|
test "solve_by_assume delegates to logic/kernel" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let st = match @kernel.ks_add_const(st0, "P", bool) {
    Ok(v) => v
    Err(_) => panic()
  }
  let p = match @kernel.ks_mk_const(st, "P") {
    Ok(v) => v
    Err(_) => panic()
  }
  let goal = mk_goal([], p)
  assert_true(solve_by_assume(st, goal) is Ok(_))
}

///|
test "solve_by_assume fails when goal constant is not in state" {
  let bool = @kernel.bool_ty()
  let st = @kernel.empty_kernel_state()
  let p = @kernel.mk_const("P", bool)
  let goal = mk_goal([], p)
  assert_true(solve_by_assume(st, goal) is Err(@kernel.TypeMismatch))
}
