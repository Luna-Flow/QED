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
  let p = @kernel.mk_const("P", bool)
  let goal = mk_goal([], p)
  assert_true(solve_by_assume(goal) is Ok(_))
}
