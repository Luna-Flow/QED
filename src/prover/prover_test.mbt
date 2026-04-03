///|

///|
using @kernel {bool_ty, empty_kernel_state, ks_add_const, ks_push_scope}

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

  assert_true(
    prove_theorem_script(st1, script1, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )
  assert_true(
    prove_theorem_script(st1, script2, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )
  assert_true(
    prove_theorem_script(st1, script3, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )
}

///|
test "prove_theorem_script respects auto_install_prelude option" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let opts = prover_options(false)
  let script = "theorem t : ⊢ P -> Q := by intro h; exact h"
  assert_true(prove_theorem_script(st1, script, opts) is Err(Sig(UnknownConst)))
}

///|
test "prove_theorem_script remains stable across later shadowing" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let script = "theorem t : ⊢ P -> P := by intro h; exact h"
  assert_true(
    prove_theorem_script(st0, script, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )

  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_prover(ks_add_const(st1, "P", bool_ty()))
  assert_true(
    prove_theorem_script(st2, script, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )
}
