///|
fn[T, E] expect_ok_tactics(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "tactics goal construction remains stable" {
  let bool = bool_ty()
  let p = mk_const("P", bool)
  let goal = mk_goal([p], p)
  assert_eq(goal_hyp_count(goal), 1)
  assert_eq(goal_hyps(goal).length(), 1)
  assert_true(goal_concl(goal) is Const("P", _, _))
}

///|
test "proof_state assumption tactic closes bridged hypothesis goals" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_tactics(ks_add_const(st0, "P", bool))
  let p = expect_ok_tactics(ks_mk_const(st1, "P"))
  let goal = mk_goal([p], p)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_tactics(
    ps_apply(st1, default_prop_prelude(), ps0, step_assumption()),
  )
  assert_true(ps_qed(ps1) is Ok(_))
}
