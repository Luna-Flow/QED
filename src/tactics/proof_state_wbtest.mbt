///|
using @kernel {empty_kernel_state, bool_ty, ks_add_const, ks_mk_const, mk_comb}

///|
using @logic {
  default_prop_prelude,
  install_prop_prelude,
  prop_mk_imp,
  logic_add_assum,
  logic_prop_imp_intro_thm,
  logic_prop_or_intro_l_thm,
  logic_prop_truth_const_thm,
}

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
