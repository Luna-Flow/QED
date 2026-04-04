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
  let wrapped = expect_ok_replay(
    logic_prop_or_wrap_left(st2, prelude, or_pq, q, base2),
  )
  let _ = expect_ok_replay(
    logic_prop_discharge_imp_prefix(st2, prelude, hyps, wrapped),
  )
}
