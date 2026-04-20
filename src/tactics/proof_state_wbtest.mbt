///|
fn[T, E] expect_ok_proof_state_wb(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "wb validate_root_theorem rejects trusted or alias tails" {
  let prelude = default_prop_prelude()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_proof_state_wb(ks_add_const(st0, "P_wb", bool_ty()))
  let st2 = expect_ok_proof_state_wb(ks_add_const(st1, "Q_wb", bool_ty()))
  let st3 = expect_ok_proof_state_wb(install_prop_prelude(st2))
  let p = expect_ok_proof_state_wb(ks_mk_const(st3, "P_wb"))
  let q = expect_ok_proof_state_wb(ks_mk_const(st3, "Q_wb"))
  let t_term = expect_ok_proof_state_wb(ks_mk_const(st3, prelude.truth_name))
  let or_c = expect_ok_proof_state_wb(ks_mk_const(st3, prelude.or_name))
  let trusted_or = mk_comb(mk_comb(or_c, t_term), q)
  let root_concl = expect_ok_proof_state_wb(
    prop_mk_imp(st3, prelude, p, trusted_or),
  )

  let th_truth = expect_ok_proof_state_wb(
    logic_prop_truth_const_thm(st3, prelude),
  )
  let th_or = expect_ok_proof_state_wb(
    logic_prop_or_intro_l_thm(st3, prelude, th_truth, q),
  )
  let th_or_with_hyp = expect_ok_proof_state_wb(logic_add_assum(st3, p, th_or))
  let th = expect_ok_proof_state_wb(
    logic_prop_imp_intro_thm(st3, prelude, p, th_or_with_hyp),
  )
  let th_concl = expect_ok_proof_state_wb(thm_concl(th))

  assert_false(term_logical_eq(th_concl, root_concl))
  assert_false(term_alpha_eq(th_concl, root_concl))
  assert_true(
    validate_root_theorem(st3, th, mk_goal([], root_concl), prelude)
    is Err(ProofSynthesisUnavailable(_)),
  )
}

///|
test "wb validate_root_theorem normalizes hypothesis sets before strict matching" {
  let prelude = default_prop_prelude()
  let st = expect_ok_proof_state_wb(install_prop_prelude(empty_kernel_state()))
  let p = expect_ok_proof_state_wb(ks_mk_const(st, prelude.truth_name))
  let th0 = expect_ok_proof_state_wb(logic_prop_truth_const_thm(st, prelude))
  let th1 = expect_ok_proof_state_wb(logic_add_assum(st, p, th0))
  assert_true(validate_root_theorem(st, th1, mk_goal([p], p), prelude) is Ok(_))
}

///|
test "wb quantified replay path can wrap a discharged implication body" {
  let prelude = default_prop_prelude()
  let st = expect_ok_proof_state_wb(install_prop_prelude(empty_kernel_state()))
  let user = mk_var("_b0", bool_ty())
  let hidden = mk_var("_b1", bool_ty())
  let th0 = expect_ok_proof_state_wb(
    logic_prop_close_hypothesis(st, [user], user),
  )
  let th1 = expect_ok_proof_state_wb(
    logic_prop_ensure_sequent(st, [user], user, th0),
  )
  assert_true(
    logic_prop_discharge_imp_prefix(st, prelude, [user], th1) is Ok(_),
  )
  let th2 = expect_ok_proof_state_wb(
    logic_prop_discharge_imp_prefix(st, prelude, [user], th1),
  )
  assert_true(
    logic_deduct_antisym(
      st,
      th2,
      expect_ok_proof_state_wb(logic_prop_truth_const_thm(st, prelude)),
    )
    is Ok(_),
  )
  let th3 = expect_ok_proof_state_wb(
    logic_deduct_antisym(
      st,
      th2,
      expect_ok_proof_state_wb(logic_prop_truth_const_thm(st, prelude)),
    ),
  )
  let th3r = expect_ok_proof_state_wb(logic_inst(st, [(user, hidden)], th3))
  let th4 = expect_ok_proof_state_wb(logic_abs_rule(st, hidden, th3r))
  assert_true(thm_concl(th4) is Ok(_))
}

///|
test "wb quantified intro exact replay works on lowered forall goal" {
  let prelude = default_prop_prelude()
  let st = expect_ok_proof_state_wb(install_prop_prelude(empty_kernel_state()))
  let x = mk_var("_b0", bool_ty())
  let body = expect_ok_proof_state_wb(prop_mk_imp(st, prelude, x, x))
  let truth = expect_ok_proof_state_wb(logic_prop_truth_const_thm(st, prelude))
  let truth_term = expect_ok_proof_state_wb(thm_concl(truth))
  let goal = expect_ok_proof_state_wb(
    mk_eq(mk_abs(x, body), mk_abs(x, truth_term)),
  )
  let ps0 = ps_init(mk_goal([], goal))
  let ps1 = expect_ok_proof_state_wb(
    ps_apply(st, prelude, ps0, step_intro("x")),
  )
  let ps2 = expect_ok_proof_state_wb(
    ps_apply(st, prelude, ps1, step_intro("h")),
  )
  match ps_current_goal(ps2) {
    Some(current) => {
      let locals = ps_current_local_hyps(ps2)
      assert_eq(locals.length(), 2)
      assert_true(term_to_string(local_hyp_term(locals[0])).contains("_b0"))
      assert_true(term_to_string(local_hyp_term(locals[1])).contains("_b0"))
      assert_true(
        term_alpha_eq(local_hyp_term(locals[0]), goal_hyps(current)[0]),
      )
      assert_true(term_alpha_eq(local_hyp_term(locals[1]), goal_concl(current)))
      let th0 = expect_ok_proof_state_wb(
        logic_prop_close_hypothesis(
          st,
          goal_hyps(current),
          local_hyp_term(locals[1]),
        ),
      )
      let th1 = expect_ok_proof_state_wb(
        logic_prop_discharge_imp_prefix(
          st,
          prelude,
          [local_hyp_term(locals[1])],
          th0,
        ),
      )
      let th_truth = expect_ok_proof_state_wb(
        logic_prop_truth_const_thm(st, prelude),
      )
      let th2 = expect_ok_proof_state_wb(
        logic_deduct_antisym(st, th1, th_truth),
      )
      let hidden = mk_var("_b1", bool_ty())
      let th2r = expect_ok_proof_state_wb(
        logic_inst(st, [(local_hyp_term(locals[0]), hidden)], th2),
      )
      let th3 = expect_ok_proof_state_wb(logic_abs_rule(st, hidden, th2r))
      assert_true(
        validate_root_theorem(st, th3, mk_goal([], goal), prelude) is Ok(_),
      )
      let ps3 = expect_ok_proof_state_wb(
        ps_apply(st, prelude, ps2, step_exact("h")),
      )
      assert_true(ps_qed(ps3) is Ok(_))
    }
    None => panic()
  }
}
