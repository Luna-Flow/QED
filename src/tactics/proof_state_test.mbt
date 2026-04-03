///|
fn[T, E] expect_ok_ps(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn expect_some_goal(goal : Goal?) -> Goal {
  match goal {
    Some(g) => g
    None => panic()
  }
}

///|
fn setup_prop_env() -> (
  @kernel.KernelState,
  @logic.PropPrelude,
  @kernel.Term,
  @kernel.Term,
  @kernel.Term,
) {
  let prelude = @logic.default_prop_prelude()
  let st = expect_ok_ps(
    @logic.install_prop_prelude(@kernel.empty_kernel_state()),
  )
  let p = @kernel.mk_var("P", @kernel.bool_ty())
  let q = @kernel.mk_var("Q", @kernel.bool_ty())
  let r = @kernel.mk_var("R", @kernel.bool_ty())
  (st, prelude, p, q, r)
}

///|
test "proof state intro + exact closes implication goal" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let imp_pp = expect_ok_ps(@logic.prop_mk_imp(st, prelude, p, p))
  let ps0 = ps_init(mk_goal([], imp_pp))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_exact("h")))
  let ps3 = expect_ok_ps(ps_apply_script(st, prelude, ps2, []))
  assert_eq(ps_goal_count(ps3), 0)
  assert_true(ps_qed(ps3) is Err(ProofSynthesisUnavailable(_)))
}

///|
test "proof state split and left/right transform goals" {
  let (st, prelude, p, q, r) = setup_prop_env()
  let and_pq = expect_ok_ps(@logic.prop_mk_and(st, prelude, p, q))
  let or_pq = expect_ok_ps(@logic.prop_mk_or(st, prelude, p, q))

  let ps0 = ps_init(mk_goal([], and_pq))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_split()))
  assert_eq(ps_goal_count(ps1), 2)
  let g_split = expect_some_goal(ps_current_goal(ps1))
  assert_true(@kernel.term_alpha_eq(goal_concl(g_split), p))

  let ps2 = ps_init(mk_goal([], or_pq))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_left()))
  let g_left = expect_some_goal(ps_current_goal(ps3))
  assert_true(@kernel.term_alpha_eq(goal_concl(g_left), p))

  let or_rq = expect_ok_ps(@logic.prop_mk_or(st, prelude, r, q))
  let ps4 = ps_init(mk_goal([], or_rq))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_right()))
  let g_right = expect_some_goal(ps_current_goal(ps5))
  assert_true(@kernel.term_alpha_eq(goal_concl(g_right), q))
}

///|
test "proof state apply supports local implication and and_elim_l pattern" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(@logic.prop_mk_imp(st, prelude, q, p))
  let imp_imp_qp_p = expect_ok_ps(@logic.prop_mk_imp(st, prelude, imp_qp, p))
  let and_pq = expect_ok_ps(@logic.prop_mk_and(st, prelude, p, q))
  let imp_and_pq_p = expect_ok_ps(@logic.prop_mk_imp(st, prelude, and_pq, p))

  let ps0 = ps_init(mk_goal([], imp_imp_qp_p))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("himp")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_apply("himp")))
  let g_local = expect_some_goal(ps_current_goal(ps2))
  assert_true(@kernel.term_alpha_eq(goal_concl(g_local), q))

  let ps3 = ps_init(mk_goal([], imp_and_pq_p))
  let ps4 = expect_ok_ps(ps_apply(st, prelude, ps3, step_intro("h")))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_apply("and_elim_l")))
  let g_rule = expect_some_goal(ps_current_goal(ps5))
  assert_true(@kernel.term_alpha_eq(goal_concl(g_rule), and_pq))
  let ps6 = expect_ok_ps(ps_apply(st, prelude, ps5, step_exact("h")))
  let ps7 = expect_ok_ps(ps_apply_script(st, prelude, ps6, []))
  assert_true(ps_qed(ps7) is Err(ProofSynthesisUnavailable(_)))
}

///|
test "proof state reports unresolved goals and malformed steps" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let ps0 = ps_init(mk_goal([], p))
  assert_true(ps_qed(ps0) is Err(UnsolvedGoals))
  assert_true(
    ps_apply(st, prelude, ps0, step_intro("h")) is Err(GoalShapeMismatch(_)),
  )

  let imp_qp = expect_ok_ps(@logic.prop_mk_imp(st, prelude, q, p))
  let ps1 = ps_init(mk_goal([], imp_qp))
  assert_true(
    ps_apply(st, prelude, ps1, step_exact("missing")) is Err(UnknownName(_)),
  )

  let ps2 = ps_init(mk_goal([], p))
  assert_true(
    ps_apply(st, prelude, ps2, step_apply("and_elim_l"))
    is Err(ApplyMismatch(_)),
  )
}

///|
test "proof state does not fabricate final theorem when goals are exhausted" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let goal = mk_goal([p], p)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_assumption()))
  assert_eq(ps_goal_count(ps1), 0)
  assert_true(ps_qed(ps1) is Err(ProofSynthesisUnavailable(_)))
}
