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
fn setup_prop_env() -> (KernelState, PropPrelude, Term, Term, Term) {
  let prelude = default_prop_prelude()
  let st = expect_ok_ps(install_prop_prelude(empty_kernel_state()))
  let p = mk_var("P", bool_ty())
  let q = mk_var("Q", bool_ty())
  let r = mk_var("R", bool_ty())
  (st, prelude, p, q, r)
}

///|
test "proof state intro + exact closes implication goal" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let imp_pp = expect_ok_ps(prop_mk_imp(st, prelude, p, p))
  let ps0 = ps_init(mk_goal([], imp_pp))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_exact("h")))
  let ps3 = expect_ok_ps(ps_apply_script(st, prelude, ps2, []))
  assert_eq(ps_goal_count(ps3), 0)
  assert_true(ps_qed(ps3) is Ok(_))
}

///|
test "proof state exact supports named theorem imp_refl" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let imp_pp = expect_ok_ps(prop_mk_imp(st, prelude, p, p))
  let ps0 = ps_init(mk_goal([], imp_pp))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_exact("imp_refl")))
  assert_eq(ps_goal_count(ps1), 0)
  assert_true(ps_qed(ps1) is Ok(_))
}

///|
test "proof state split and left/right transform goals" {
  let (st, prelude, p, q, r) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let or_pq = expect_ok_ps(prop_mk_or(st, prelude, p, q))

  let ps0 = ps_init(mk_goal([], and_pq))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_split()))
  assert_eq(ps_goal_count(ps1), 2)
  let g_split = expect_some_goal(ps_current_goal(ps1))
  assert_true(term_alpha_eq(goal_concl(g_split), p))

  let ps2 = ps_init(mk_goal([], or_pq))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_left()))
  let g_left = expect_some_goal(ps_current_goal(ps3))
  assert_true(term_alpha_eq(goal_concl(g_left), p))

  let or_rq = expect_ok_ps(prop_mk_or(st, prelude, r, q))
  let ps4 = ps_init(mk_goal([], or_rq))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_right()))
  let g_right = expect_some_goal(ps_current_goal(ps5))
  assert_true(term_alpha_eq(goal_concl(g_right), q))
}

///|
test "proof state apply supports local implication and and_elim_l pattern" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let imp_imp_qp_p = expect_ok_ps(prop_mk_imp(st, prelude, imp_qp, p))
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let imp_and_pq_p = expect_ok_ps(prop_mk_imp(st, prelude, and_pq, p))

  let ps0 = ps_init(mk_goal([], imp_imp_qp_p))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("himp")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_apply("himp")))
  let g_local = expect_some_goal(ps_current_goal(ps2))
  assert_true(term_alpha_eq(goal_concl(g_local), q))

  let ps3 = ps_init(mk_goal([], imp_and_pq_p))
  let ps4 = expect_ok_ps(ps_apply(st, prelude, ps3, step_intro("h")))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_apply("and_elim_l")))
  let g_rule = expect_some_goal(ps_current_goal(ps5))
  assert_true(term_alpha_eq(goal_concl(g_rule), and_pq))
  let ps6 = expect_ok_ps(ps_apply(st, prelude, ps5, step_exact("h")))
  let ps7 = expect_ok_ps(ps_apply_script(st, prelude, ps6, []))
  assert_true(ps_qed(ps7) is Ok(_))
}

///|
test "proof state theorem-backed apply reconstructs final implication theorem" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, and_pq, p))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_apply("and_elim_l")))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_exact("h")))
  let th = expect_ok_ps(ps_qed(ps3))
  let concl = expect_ok_ps(thm_concl(th))
  assert_true(term_logical_eq(concl, target) || term_alpha_eq(concl, target))
}

///|
test "proof state and_elim_l closes when P Q are kernel constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_ps(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_ps(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st))
  let p = expect_ok_ps(ks_mk_const(st2, "P"))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let and_pq = expect_ok_ps(prop_mk_and(st2, prelude, p, q))
  let imp_and_pq_p = expect_ok_ps(prop_mk_imp(st2, prelude, and_pq, p))
  let ps0 = ps_init(mk_goal([], imp_and_pq_p))
  let ps1 = expect_ok_ps(ps_apply(st2, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st2, prelude, ps1, step_apply("and_elim_l")))
  let ps3 = expect_ok_ps(ps_apply(st2, prelude, ps2, step_exact("h")))
  let ps4 = expect_ok_ps(ps_apply_script(st2, prelude, ps3, []))
  assert_true(ps_qed(ps4) is Ok(_))
}

///|
test "proof state and_elim_r closes when P Q are kernel constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_ps(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_ps(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st))
  let p = expect_ok_ps(ks_mk_const(st2, "P"))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let and_pq = expect_ok_ps(prop_mk_and(st2, prelude, p, q))
  let imp_and_pq_q = expect_ok_ps(prop_mk_imp(st2, prelude, and_pq, q))
  let ps0 = ps_init(mk_goal([], imp_and_pq_q))
  let ps1 = expect_ok_ps(ps_apply(st2, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st2, prelude, ps1, step_apply("and_elim_r")))
  let ps3 = expect_ok_ps(ps_apply(st2, prelude, ps2, step_exact("h")))
  let ps4 = expect_ok_ps(ps_apply_script(st2, prelude, ps3, []))
  assert_true(ps_qed(ps4) is Ok(_))
}

///|
test "proof state apply supports theorem-backed or intro names" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_ps(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_ps(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st))
  let p = expect_ok_ps(ks_mk_const(st2, "P"))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let or_pq = expect_ok_ps(prop_mk_or(st2, prelude, p, q))
  let imp_p_or = expect_ok_ps(prop_mk_imp(st2, prelude, p, or_pq))
  let ps0 = ps_init(mk_goal([], imp_p_or))
  let ps1 = expect_ok_ps(ps_apply(st2, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st2, prelude, ps1, step_apply("or_intro_l")))
  let g_apply = expect_some_goal(ps_current_goal(ps2))
  assert_true(term_alpha_eq(goal_concl(g_apply), p))
  let ps3 = expect_ok_ps(ps_apply(st2, prelude, ps2, step_exact("h")))
  assert_true(ps_qed(ps3) is Ok(_))
}

///|
test "proof state apply supports theorem-backed or_intro_r" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_ps(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_ps(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st))
  let p = expect_ok_ps(ks_mk_const(st2, "P"))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let or_pq = expect_ok_ps(prop_mk_or(st2, prelude, p, q))
  let imp_q_or = expect_ok_ps(prop_mk_imp(st2, prelude, q, or_pq))
  let ps0 = ps_init(mk_goal([], imp_q_or))
  let ps1 = expect_ok_ps(ps_apply(st2, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st2, prelude, ps1, step_apply("or_intro_r")))
  let g_apply = expect_some_goal(ps_current_goal(ps2))
  assert_true(term_alpha_eq(goal_concl(g_apply), q))
  let ps3 = expect_ok_ps(ps_apply(st2, prelude, ps2, step_exact("h")))
  assert_true(ps_qed(ps3) is Ok(_))
}

///|
test "proof state apply imp_intro mirrors implication introduction" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, imp_qp))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_apply("imp_intro")))
  let g1 = expect_some_goal(ps_current_goal(ps1))
  assert_true(term_alpha_eq(goal_concl(g1), imp_qp))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_intro("hq")))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_exact("_h")))
  let th = expect_ok_ps(ps_qed(ps3))
  let concl = expect_ok_ps(thm_concl(th))
  assert_true(term_logical_eq(concl, target) || term_alpha_eq(concl, target))
}

///|
test "proof state apply imp_elim uses context implication eliminator" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, imp_qp, imp_qp))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("himp")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_intro("hq")))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_apply("imp_elim")))
  let g3 = expect_some_goal(ps_current_goal(ps3))
  assert_true(term_alpha_eq(goal_concl(g3), q))
  let ps4 = expect_ok_ps(ps_apply(st, prelude, ps3, step_exact("hq")))
  let th = expect_ok_ps(ps_qed(ps4))
  let concl = expect_ok_ps(thm_concl(th))
  assert_true(term_logical_eq(concl, target) || term_alpha_eq(concl, target))
}

///|
test "proof state apply and_intro splits conjunction goals" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let imp_q_and = expect_ok_ps(prop_mk_imp(st, prelude, q, and_pq))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, imp_q_and))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("hp")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_intro("hq")))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_apply("and_intro")))
  assert_eq(ps_goal_count(ps3), 2)
  let g3 = expect_some_goal(ps_current_goal(ps3))
  assert_true(term_alpha_eq(goal_concl(g3), p))
  let ps4 = expect_ok_ps(ps_apply(st, prelude, ps3, step_exact("hp")))
  let g4 = expect_some_goal(ps_current_goal(ps4))
  assert_true(term_alpha_eq(goal_concl(g4), q))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_exact("hq")))
  let th = expect_ok_ps(ps_qed(ps5))
  let concl = expect_ok_ps(thm_concl(th))
  assert_true(term_logical_eq(concl, target) || term_alpha_eq(concl, target))
}

///|
fn setup_or_intro_const_ps() -> (KernelState, PropPrelude, ProofState) {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_ps(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_ps(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st))
  let p = expect_ok_ps(ks_mk_const(st2, "P"))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let or_pq = expect_ok_ps(prop_mk_or(st2, prelude, p, q))
  let imp_p_or = expect_ok_ps(prop_mk_imp(st2, prelude, p, or_pq))
  let ps0 = ps_init(mk_goal([], imp_p_or))
  let ps1 = expect_ok_ps(ps_apply(st2, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st2, prelude, ps1, step_left()))
  (st2, prelude, ps2)
}

///|
test "proof state left closes P -> P or Q with kernel constants" {
  let (st2, prelude, ps2) = setup_or_intro_const_ps()
  let ps3 = expect_ok_ps(ps_apply(st2, prelude, ps2, step_exact("h")))
  assert_eq(ps_goal_count(ps3), 0)
  assert_true(ps_qed(ps3) is Ok(_))
}

///|
test "proof state left reconstructs wrapped disjunction theorem" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let or_pq = expect_ok_ps(prop_mk_or(st, prelude, p, q))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, or_pq))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("h")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_left()))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_exact("h")))
  let th = expect_ok_ps(ps_qed(ps3))
  let concl = expect_ok_ps(thm_concl(th))
  let concl_nf = match logic_beta_nf_bool_term_deep(st, concl) {
    Ok(v) => v
    Err(_) => concl
  }
  match prop_dest_imp(st, prelude, concl_nf) {
    Some((lhs, rhs)) => {
      assert_true(term_alpha_eq(lhs, p))
      match prop_dest_or(st, prelude, rhs) {
        Some((or_lhs, _)) => assert_true(term_alpha_eq(or_lhs, p))
        None => panic()
      }
    }
    None => panic()
  }
}

///|
test "proof state split reconstructs conjunction under implication prefixes" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let imp_q_and = expect_ok_ps(prop_mk_imp(st, prelude, q, and_pq))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, imp_q_and))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("hp")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_intro("hq")))
  let ps3 = expect_ok_ps(ps_apply(st, prelude, ps2, step_split()))
  let ps4 = expect_ok_ps(ps_apply(st, prelude, ps3, step_exact("hp")))
  let ps5 = expect_ok_ps(ps_apply(st, prelude, ps4, step_exact("hq")))
  let th = expect_ok_ps(ps_qed(ps5))
  let concl = expect_ok_ps(thm_concl(th))
  assert_true(term_logical_eq(concl, target) || term_alpha_eq(concl, target))
}

///|
test "proof state reports unresolved goals and malformed steps" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let ps0 = ps_init(mk_goal([], p))
  assert_true(ps_qed(ps0) is Err(UnsolvedGoals))
  assert_true(
    ps_apply(st, prelude, ps0, step_intro("h")) is Err(GoalShapeMismatch(_)),
  )

  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let ps1 = ps_init(mk_goal([], imp_qp))
  assert_true(
    ps_apply(st, prelude, ps1, step_exact("missing")) is Err(UnknownName(_)),
  )

  let ps2 = ps_init(mk_goal([], p))
  assert_true(
    ps_apply(st, prelude, ps2, step_apply("and_elim_l"))
    is Err(ApplyMismatch(_)),
  )

  let imp_pp = expect_ok_ps(prop_mk_imp(st, prelude, p, p))
  let ps3 = ps_init(mk_goal([], imp_pp))
  assert_true(
    ps_apply(st, prelude, ps3, step_apply("imp_refl")) is Err(ApplyMismatch(_)),
  )
}

///|
test "proof state assumption produces checked theorem matching goal" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let goal = mk_goal([p], p)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_assumption()))
  assert_eq(ps_goal_count(ps1), 0)
  let th = expect_ok_ps(ps_qed(ps1))
  let c = expect_ok_ps(thm_concl(th))
  assert_true(term_alpha_eq(c, p))
}

///|
test "proof state local names still win over named theorem references" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let imp_pp = expect_ok_ps(prop_mk_imp(st, prelude, p, p))
  let goal = mk_goal([], imp_pp)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("imp_refl")))
  let g1 = expect_some_goal(ps_current_goal(ps1))
  assert_true(term_alpha_eq(goal_concl(g1), p))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_exact("imp_refl")))
  assert_true(ps_qed(ps2) is Ok(_))
}

///|
test "proof state apply prefers local implication over theorem name collision" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let imp_imp_qp_p = expect_ok_ps(prop_mk_imp(st, prelude, imp_qp, p))
  let ps0 = ps_init(mk_goal([], imp_imp_qp_p))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("and_elim_l")))
  let ps2 = expect_ok_ps(ps_apply(st, prelude, ps1, step_apply("and_elim_l")))
  let g2 = expect_some_goal(ps_current_goal(ps2))
  assert_true(term_alpha_eq(goal_concl(g2), q))
}

///|
test "proof state exact supports context-derived theorem names" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let goal = mk_goal([and_pq], p)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_exact("and_elim_l")))
  let th = expect_ok_ps(ps_qed(ps1))
  let c = expect_ok_ps(thm_concl(th))
  assert_true(term_alpha_eq(c, p))
}

///|
test "proof state exact supports truth and ex_falso theorem names" {
  let prelude = default_prop_prelude()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_ps(ks_add_const(st0, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st1))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let t_term = expect_ok_ps(ks_mk_const(st2, prelude.truth_name))
  let f_term = expect_ok_ps(ks_mk_const(st2, prelude.false_name))

  let ps_truth = ps_init(mk_goal([], t_term))
  let ps_truth_done = expect_ok_ps(
    ps_apply(st2, prelude, ps_truth, step_exact("truth")),
  )
  assert_true(ps_qed(ps_truth_done) is Ok(_))

  let ps_false = ps_init(mk_goal([f_term], q))
  let ps_false_done = expect_ok_ps(
    ps_apply(st2, prelude, ps_false, step_exact("ex_falso")),
  )
  let th_false = expect_ok_ps(ps_qed(ps_false_done))
  let c_false = expect_ok_ps(thm_concl(th_false))
  assert_true(term_alpha_eq(c_false, q))
}

///|
test "proof state exact supports context-derived not_elim" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let false_term = expect_ok_ps(ks_mk_const(st, prelude.false_name))
  let not_p = expect_ok_ps(prop_mk_not(st, prelude, p))
  let goal = mk_goal([not_p, p], false_term)
  let ps0 = ps_init(goal)
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_exact("not_elim")))
  let th = expect_ok_ps(ps_qed(ps1))
  let c = expect_ok_ps(thm_concl(th))
  assert_true(term_alpha_eq(c, false_term))
}

///|
test "proof state exact supports witness-based theorem names" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let and_pq = expect_ok_ps(prop_mk_and(st, prelude, p, q))
  let imp_pq = expect_ok_ps(prop_mk_imp(st, prelude, p, q))
  let eq_pp = expect_ok_ps(mk_eq(p, p))
  let eq_pq = expect_ok_ps(mk_eq(p, q))
  let eq_qp = expect_ok_ps(mk_eq(q, p))

  let ps_and = ps_init(mk_goal([p, q], and_pq))
  let ps_and_done = expect_ok_ps(
    ps_apply(st, prelude, ps_and, step_exact("and_intro")),
  )
  assert_true(ps_qed(ps_and_done) is Ok(_))

  let ps_imp = ps_init(mk_goal([imp_pq, p], q))
  let ps_imp_done = expect_ok_ps(
    ps_apply(st, prelude, ps_imp, step_exact("imp_elim")),
  )
  assert_true(ps_qed(ps_imp_done) is Ok(_))

  let ps_refl = ps_init(mk_goal([], eq_pp))
  let ps_refl_done = expect_ok_ps(
    ps_apply(st, prelude, ps_refl, step_exact("eq_refl")),
  )
  assert_true(ps_qed(ps_refl_done) is Ok(_))

  let ps_sym = ps_init(mk_goal([eq_qp], eq_pq))
  let ps_sym_done = expect_ok_ps(
    ps_apply(st, prelude, ps_sym, step_exact("eq_sym")),
  )
  assert_true(ps_qed(ps_sym_done) is Ok(_))

  let ps_mp = ps_init(mk_goal([eq_pq, p], q))
  let ps_mp_done = expect_ok_ps(
    ps_apply(st, prelude, ps_mp, step_exact("eq_mp")),
  )
  assert_true(ps_qed(ps_mp_done) is Ok(_))
}

///|
test "proof state apply rejects direct-close theorem names" {
  let prelude = default_prop_prelude()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_ps(ks_add_const(st0, "Q", bool_ty()))
  let st2 = expect_ok_ps(install_prop_prelude(st1))
  let q = expect_ok_ps(ks_mk_const(st2, "Q"))
  let t_term = expect_ok_ps(ks_mk_const(st2, prelude.truth_name))
  let f_term = expect_ok_ps(ks_mk_const(st2, prelude.false_name))

  let ps_truth = ps_init(mk_goal([], t_term))
  assert_true(
    ps_apply(st2, prelude, ps_truth, step_apply("truth"))
    is Err(ApplyMismatch(_)),
  )

  let ps_false = ps_init(mk_goal([f_term], q))
  assert_true(
    ps_apply(st2, prelude, ps_false, step_apply("ex_falso"))
    is Err(ApplyMismatch(_)),
  )

  let (st3, prelude3, p, _, _) = setup_prop_env()
  let false_term = expect_ok_ps(ks_mk_const(st3, prelude3.false_name))
  let not_p = expect_ok_ps(prop_mk_not(st3, prelude3, p))
  let ps_not = ps_init(mk_goal([not_p, p], false_term))
  assert_true(
    ps_apply(st3, prelude3, ps_not, step_apply("not_elim"))
    is Err(ApplyMismatch(_)),
  )

  let ps_missing = ps_init(mk_goal([], q))
  assert_true(
    ps_apply(st2, prelude, ps_missing, step_apply("missing"))
    is Err(UnknownName(_)),
  )
}

///|
test "proof state exact rejects apply-only or context-missing theorem names" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let or_pq = expect_ok_ps(prop_mk_or(st, prelude, p, q))
  let imp_p_or = expect_ok_ps(prop_mk_imp(st, prelude, p, or_pq))
  let ps_apply_only = ps_init(mk_goal([], imp_p_or))
  assert_true(
    ps_apply(st, prelude, ps_apply_only, step_exact("or_intro_l"))
    is Err(GoalShapeMismatch(_)),
  )

  let ps_missing_ctx = ps_init(mk_goal([p], p))
  assert_true(
    ps_apply(st, prelude, ps_missing_ctx, step_exact("and_elim_l"))
    is Err(GoalShapeMismatch(_)),
  )
}

///|
test "proof state exact local hypothesis must directly witness current goal" {
  let (st, prelude, p, q, _) = setup_prop_env()
  let imp_qp = expect_ok_ps(prop_mk_imp(st, prelude, q, p))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, imp_qp))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("hp")))
  assert_true(
    ps_apply(st, prelude, ps1, step_exact("hp")) is Err(GoalShapeMismatch(_)),
  )
}

///|
test "proof state exact does not fall through past shadowing local witness names" {
  let (st, prelude, p, _, _) = setup_prop_env()
  let t_term = expect_ok_ps(ks_mk_const(st, prelude.truth_name))
  let target = expect_ok_ps(prop_mk_imp(st, prelude, p, t_term))
  let ps0 = ps_init(mk_goal([], target))
  let ps1 = expect_ok_ps(ps_apply(st, prelude, ps0, step_intro("truth")))
  assert_true(
    ps_apply(st, prelude, ps1, step_exact("truth")) is Err(GoalShapeMismatch(_)),
  )
}
