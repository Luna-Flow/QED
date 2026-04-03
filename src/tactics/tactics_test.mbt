///|
using @kernel {
  bool_ty,
  empty_kernel_state,
  ks_add_const,
  ks_mk_const,
  mk_const,
  mk_eq,
  mk_tyvar,
  mk_var,
}

///|
using @logic {logic_assume}

///|
fn[T, E] expect_ok_tactics(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "tactics goal construction" {
  let bool = bool_ty()
  let p = mk_const("P", bool)
  let goal = mk_goal([p], p)
  assert_eq(goal_hyp_count(goal), 1)
  assert_eq(goal_hyps(goal).length(), 1)
  assert_true(goal_concl(goal) is Const("P", _, _))
}

///|
test "solve_by_assume delegates to logic/kernel" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st = match ks_add_const(st0, "P", bool) {
    Ok(v) => v
    Err(_) => panic()
  }
  let p = match ks_mk_const(st, "P") {
    Ok(v) => v
    Err(_) => panic()
  }
  let goal = mk_goal([], p)
  assert_true(solve_by_assume(st, goal) is Ok(_))
}

///|
test "solve_by_assume fails when goal constant is not in state" {
  let bool = bool_ty()
  let st = empty_kernel_state()
  let p = mk_const("P", bool)
  let goal = mk_goal([], p)
  assert_true(solve_by_assume(st, goal) is Err(TypeMismatch))
}

///|
test "solve_by_refl delegates to logic/kernel" {
  let st = empty_kernel_state()
  let x = mk_var("x", mk_tyvar("A"))
  assert_true(solve_by_refl(st, x) is Ok(_))
}

///|
test "solve_by_trans composes equalities and reports mismatch" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let eq_xy = expect_ok_tactics(mk_eq(x, y))
  let eq_yz = expect_ok_tactics(mk_eq(y, z))
  let eq_zx = expect_ok_tactics(mk_eq(z, x))

  let th_xy = expect_ok_tactics(logic_assume(st, eq_xy))
  let th_yz = expect_ok_tactics(logic_assume(st, eq_yz))
  let th_zx = expect_ok_tactics(logic_assume(st, eq_zx))

  assert_true(solve_by_trans(st, th_xy, th_yz) is Ok(_))
  assert_true(solve_by_trans(st, th_xy, th_zx) is Err(AlphaMismatch))
}

///|
test "solve_by_hyp finds alpha-equal hypothesis or fails" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_tactics(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_tactics(ks_add_const(st1, "Q", bool))
  let p = expect_ok_tactics(ks_mk_const(st2, "P"))
  let q = expect_ok_tactics(ks_mk_const(st2, "Q"))

  let goal_hit = mk_goal([q, p], p)
  let goal_miss = mk_goal([q], p)
  assert_true(solve_by_hyp(st2, goal_hit) is Ok(_))
  assert_true(solve_by_hyp(st2, goal_miss) is Err(AlphaMismatch))
}
