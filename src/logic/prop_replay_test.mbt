///|
fn[T, E] expect_ok_replay(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn setup_replay_env() -> (KernelState, PropPrelude, Term, Term, Term) {
  let prelude = default_prop_prelude()
  let st = expect_ok_replay(install_prop_prelude(empty_kernel_state()))
  let p = mk_var("P", bool_ty())
  let q = mk_var("Q", bool_ty())
  let r = mk_var("R", bool_ty())
  (st, prelude, p, q, r)
}

///|
fn replay_test_term_compat(state : KernelState, lhs : Term, rhs : Term) -> Bool {
  if term_logical_eq(lhs, rhs) || term_alpha_eq(lhs, rhs) {
    true
  } else {
    let lhs_nf = expect_ok_replay(logic_beta_nf_bool_term_deep(state, lhs))
    let rhs_nf = expect_ok_replay(logic_beta_nf_bool_term_deep(state, rhs))
    term_logical_eq(lhs_nf, rhs_nf) || term_alpha_eq(lhs_nf, rhs_nf)
  }
}

///|
test "prop replay stable subset wraps assume" {
  let (st, _prelude, p, _q, _) = setup_replay_env()
  let th_p = expect_ok_replay(logic_prop_assume(st, p))
  match thm_concl(th_p) {
    Ok(concl) => assert_true(term_alpha_eq(concl, p))
    Err(_) => panic()
  }
}

///|
test "prop replay imp intro works on bool constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_replay(ks_add_const(s0, "Pbb", bool_ty()))
  let st = expect_ok_replay(install_prop_prelude(s1))
  let p = expect_ok_replay(ks_mk_const(st, "Pbb"))
  let ta = expect_ok_replay(logic_prop_assume(st, p))
  let _and = expect_ok_replay(logic_prop_and_intro_thm(st, prelude, ta, ta))
  let _th_refl = expect_ok_replay(logic_prop_imp_refl(st, prelude, p))
  let th_body = expect_ok_replay(logic_prop_assume(st, p))
  let _th_imp = expect_ok_replay(
    logic_prop_imp_intro_thm(st, prelude, p, th_body),
  )
}

///|
test "prop replay or_wrap_left matches tactics kernel constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_replay(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_replay(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_replay(install_prop_prelude(st))
  let p = expect_ok_replay(ks_mk_const(st2, "P"))
  let q = expect_ok_replay(ks_mk_const(st2, "Q"))
  let or_pq = expect_ok_replay(prop_mk_or(st2, prelude, p, q))
  let hyps : Array[Term] = [p]
  let base = expect_ok_replay(logic_prop_close_hypothesis(st2, hyps, p))
  let base2 = expect_ok_replay(logic_prop_ensure_sequent(st2, hyps, p, base))
  let direct = expect_ok_replay(
    logic_prop_or_intro_l_thm(st2, prelude, base2, q),
  )
  let direct_concl = expect_ok_replay(thm_concl(direct))
  let direct_nf = expect_ok_replay(
    logic_beta_nf_bool_term_deep(st2, direct_concl),
  )
  let or_nf = expect_ok_replay(logic_beta_nf_bool_term_deep(st2, or_pq))
  match
    (prop_dest_or(st2, prelude, direct_nf), prop_dest_or(st2, prelude, or_nf)) {
    (Some((left_direct, right_direct)), Some((left_goal, right_goal))) => {
      assert_true(replay_test_term_compat(st2, left_direct, left_goal))
      assert_true(replay_test_term_compat(st2, right_direct, right_goal))
    }
    _ => panic()
  }
  let wrapped = expect_ok_replay(
    logic_prop_or_wrap_left(st2, prelude, or_pq, q, base2),
  )
  let _ = expect_ok_replay(
    logic_prop_discharge_imp_prefix(st2, prelude, hyps, wrapped),
  )
}

///|
test "prop replay or_wrap validates full disjunction target" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_replay(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_replay(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_replay(install_prop_prelude(st))
  let p = expect_ok_replay(ks_mk_const(st2, "P"))
  let q = expect_ok_replay(ks_mk_const(st2, "Q"))
  let or_pq = expect_ok_replay(prop_mk_or(st2, prelude, p, q))
  let or_qp = expect_ok_replay(prop_mk_or(st2, prelude, q, p))
  let th_p = expect_ok_replay(logic_prop_assume(st2, p))
  let th_q = expect_ok_replay(logic_prop_assume(st2, q))
  assert_true(logic_prop_or_wrap_left(st2, prelude, or_qp, q, th_p) is Err(_))
  assert_true(logic_prop_or_wrap_right(st2, prelude, or_qp, p, th_q) is Err(_))
  assert_true(logic_prop_or_wrap_right(st2, prelude, or_pq, p, th_q) is Ok(_))
}
