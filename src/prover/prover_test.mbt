///|

///|
fn[T, E] expect_ok_prover(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "prove_theorem_script runs linear scripts with auto prelude install" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))

  let script1 = "theorem t1 : ⊢ P -> P := by intro h; exact h"
  let script2 = "theorem t2 : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h"
  let script3 = "theorem t3 : ⊢ P -> P ∨ Q := by intro h; left; exact h"

  let (st_out1, th1) = expect_ok_prover(
    prove_theorem_script(st1, script1, default_prover_options()),
  )
  let p = expect_ok_prover(ks_mk_const(st_out1, "P"))
  let q = expect_ok_prover(ks_mk_const(st_out1, "Q"))
  let prelude = default_prop_prelude()
  let imp_pp = expect_ok_prover(prop_mk_imp(st_out1, prelude, p, p))
  let c1 = expect_ok_prover(thm_concl(th1))
  assert_true(term_logical_eq(c1, imp_pp))

  let (st_out2, th2) = expect_ok_prover(
    prove_theorem_script(st_out1, script2, default_prover_options()),
  )
  let and_pq = expect_ok_prover(prop_mk_and(st_out2, prelude, p, q))
  let imp_and_p = expect_ok_prover(prop_mk_imp(st_out2, prelude, and_pq, p))
  let c2 = expect_ok_prover(thm_concl(th2))
  assert_true(term_logical_eq(c2, imp_and_p))

  let _ = expect_ok_prover(
    prove_theorem_script(st_out2, script3, default_prover_options()),
  )
}

///|
test "prove_theorem_script respects auto_install_prelude option" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let st_pre = expect_ok_prover(install_prop_prelude(st1))
  let opts = prover_options(false)
  let script = "theorem t : ⊢ P -> P := by intro h; exact h"
  assert_true(prove_theorem_script(st_pre, script, opts) is Ok(_))
}

///|
test "prove_theorem_script remains stable across later shadowing" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let script = "theorem t : ⊢ P -> P := by intro h; exact h"
  assert_true(
    prove_theorem_script(st0, script, default_prover_options()) is Ok(_),
  )

  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_prover(ks_add_const(st1, "P", bool_ty()))
  assert_true(
    prove_theorem_script(st2, script, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script does not treat ordinary imp application as trusted implication" {
  let bool = bool_ty()
  let bin = fun_ty(bool, fun_ty(bool, bool))
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool))
  let st1 = expect_ok_prover(ks_add_const(st0, "imp", bin))
  let script = "theorem t : ⊢ imp P P := by intro h; exact h"
  assert_true(
    prove_theorem_script(st1, script, prover_options(false))
    is Err(Tactic(GoalShapeMismatch(_))),
  )
}
