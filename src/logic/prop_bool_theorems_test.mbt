///|
fn[T, E] expect_ok_bool_asset(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn setup_bool_asset_env() -> (KernelState, PropPrelude, Term, Term, Term) {
  let prelude = default_prop_prelude()
  let st = expect_ok_bool_asset(install_prop_prelude(empty_kernel_state()))
  let p = mk_var("P", bool_ty())
  let q = mk_var("Q", bool_ty())
  let r = mk_var("R", bool_ty())
  (st, prelude, p, q, r)
}

///|
test "bool theorem layer exposes truth and false assets" {
  let (st, prelude, _, _, _) = setup_bool_asset_env()
  let th_t = expect_ok_bool_asset(logic_prop_truth_thm(st))
  let th_f = expect_ok_bool_asset(logic_bool_false_def_thm(st, prelude))
  assert_eq(thm_hyp_count(th_t), 0)
  assert_eq(thm_hyp_count(th_f), 0)
  assert_true(thm_concl(th_t) is Ok(_))
  assert_true(thm_concl(th_f) is Ok(_))
}

///|
test "bool and_intro accepts two assumption theorems" {
  let (st, prelude, p, q, _) = setup_bool_asset_env()
  let ta = expect_ok_bool_asset(logic_assume(st, p))
  let tb = expect_ok_bool_asset(logic_assume(st, q))
  let _ = expect_ok_bool_asset(logic_prop_and_intro_thm(st, prelude, ta, tb))
}

///|
test "bool ex_falso works after not_elim with free bool variables" {
  let (st2, prelude, p, q, _) = setup_bool_asset_env()
  let not_p = expect_ok_bool_asset(prop_mk_not(st2, prelude, p))
  let th_not = expect_ok_bool_asset(logic_assume(st2, not_p))
  let th_p = expect_ok_bool_asset(logic_assume(st2, p))
  let th_false = expect_ok_bool_asset(
    logic_prop_not_elim(st2, prelude, th_not, th_p),
  )
  let _ = expect_ok_bool_asset(
    logic_prop_ex_falso_thm(st2, prelude, th_false, q),
  )
}

///|
test "bool ex_falso works after not_elim on kernel bool constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_bool_asset(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_bool_asset(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_bool_asset(install_prop_prelude(st))
  let p = expect_ok_bool_asset(ks_mk_const(st2, "P"))
  let q = expect_ok_bool_asset(ks_mk_const(st2, "Q"))
  let not_p = expect_ok_bool_asset(prop_mk_not(st2, prelude, p))
  let th_not = expect_ok_bool_asset(logic_assume(st2, not_p))
  let th_p = expect_ok_bool_asset(logic_assume(st2, p))
  let th_false = expect_ok_bool_asset(
    logic_prop_not_elim(st2, prelude, th_not, th_p),
  )
  let _ = expect_ok_bool_asset(
    logic_prop_ex_falso_thm(st2, prelude, th_false, q),
  )
}

///|
test "bool not_elim works with kernel bool constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_bool_asset(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_bool_asset(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_bool_asset(install_prop_prelude(st))
  let p = expect_ok_bool_asset(ks_mk_const(st2, "P"))
  let not_p = expect_ok_bool_asset(prop_mk_not(st2, prelude, p))
  let th_not = expect_ok_bool_asset(logic_assume(st2, not_p))
  let th_p = expect_ok_bool_asset(logic_assume(st2, p))
  let _ = expect_ok_bool_asset(logic_prop_not_elim(st2, prelude, th_not, th_p))
}

///|
test "bool imp_intro after ex_falso on kernel bool constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_bool_asset(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_bool_asset(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_bool_asset(install_prop_prelude(st))
  let p = expect_ok_bool_asset(ks_mk_const(st2, "P"))
  let q = expect_ok_bool_asset(ks_mk_const(st2, "Q"))
  let not_p = expect_ok_bool_asset(prop_mk_not(st2, prelude, p))
  let th_not_p = expect_ok_bool_asset(logic_assume(st2, not_p))
  let th_p = expect_ok_bool_asset(logic_assume(st2, p))
  let th_false = expect_ok_bool_asset(
    logic_prop_not_elim(st2, prelude, th_not_p, th_p),
  )
  let th_q = expect_ok_bool_asset(
    logic_prop_ex_falso_thm(st2, prelude, th_false, q),
  )
  let _ = expect_ok_bool_asset(
    logic_prop_imp_intro_thm(st2, prelude, not_p, th_q),
  )
}

///|
test "bool or_intro_l works with kernel bool constants" {
  let prelude = default_prop_prelude()
  let s0 = empty_kernel_state()
  let s1 = expect_ok_bool_asset(ks_add_const(s0, "P", bool_ty()))
  let st = expect_ok_bool_asset(ks_add_const(s1, "Q", bool_ty()))
  let st2 = expect_ok_bool_asset(install_prop_prelude(st))
  let p = expect_ok_bool_asset(ks_mk_const(st2, "P"))
  let q = expect_ok_bool_asset(ks_mk_const(st2, "Q"))
  let th_p = expect_ok_bool_asset(logic_assume(st2, p))
  let th_or = expect_ok_bool_asset(
    logic_prop_or_intro_l_thm(st2, prelude, th_p, q),
  )
  let hyps_p : Array[Term] = [p]
  let _ = expect_ok_bool_asset(
    logic_prop_discharge_imp_prefix(st2, prelude, hyps_p, th_or),
  )
}
