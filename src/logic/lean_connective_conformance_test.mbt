// Conformance tests for the connective constructors of `inductive Derivation`
// in formal_verification/QEDFV/HOL/Derivation.lean.
//
// Lean takes truth, falsity, conjunction and implication as primitive term
// formers with their own rules. The kernel defines them as prelude constants
// and this package derives the same rules (see ConnectiveRules.lean). Each test
// is named `Derivation.<constructor>: ...` and checks the conclusion and
// hypotheses the constructor states, plus each of its premises.

///|
fn[T, E] lcc_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn lcc_env() -> (KernelState, PropPrelude, Term, Term, Term) {
  let st = lcc_ok(install_prop_prelude(empty_kernel_state()))
  (
    st,
    default_prop_prelude(),
    mk_var("p", bool_ty()),
    mk_var("q", bool_ty()),
    mk_var("r", bool_ty()),
  )
}

///|
fn lcc_concl_is(th : Thm, expected : Term) -> Bool {
  term_alpha_eq(lcc_ok(thm_concl(th)), expected)
}

///|
/// Set equality of hypotheses modulo alpha-equivalence.
fn lcc_hyps_are(th : Thm, expected : Array[Term]) -> Bool {
  let hyps = lcc_ok(thm_hyps(th))
  hyps.all(h => expected.any(e => term_alpha_eq(h, e))) &&
  expected.all(e => hyps.any(h => term_alpha_eq(h, e)))
}

///|
test "Derivation.truthIntro: concludes T with no hypotheses" {
  let (st, prelude, _, _, _) = lcc_env()
  let th = lcc_ok(logic_prop_truth_const_thm(st, prelude))
  let truth = lcc_ok(ks_mk_const(st, prop_truth_name(prelude)))
  assert_true(lcc_concl_is(th, truth))
  assert_true(lcc_hyps_are(th, []))
}

///|
test "Derivation.falsityElim: concludes any q from F with the same hypotheses" {
  let (st, prelude, p, q, _) = lcc_env()
  let not_p = lcc_ok(prop_mk_not(st, prelude, p))
  let th_false = lcc_ok(
    logic_prop_not_elim(
      st,
      prelude,
      lcc_ok(logic_assume(st, not_p)),
      lcc_ok(logic_assume(st, p)),
    ),
  )
  // The derived rules work on the unfolded definition of F.
  assert_true(lcc_concl_is(th_false, logic_prop_false_term()))
  let th = lcc_ok(logic_prop_ex_falso_thm(st, prelude, th_false, q))
  assert_true(lcc_concl_is(th, q))
  assert_true(lcc_hyps_are(th, [not_p, p]))
}

///|
test "Derivation.falsityElim: premise A.concl = F is enforced" {
  let (st, prelude, p, q, _) = lcc_env()
  let th_p = lcc_ok(logic_assume(st, p))
  assert_true(logic_prop_ex_falso_thm(st, prelude, th_p, q) is Err(_))
}

///|
test "Derivation.conjIntro: concludes p ∧ q over the union of hypotheses" {
  let (st, prelude, p, q, r) = lcc_env()
  let th_p = lcc_ok(logic_add_assum(st, r, lcc_ok(logic_assume(st, p))))
  let th_q = lcc_ok(logic_assume(st, q))
  let th = lcc_ok(logic_prop_and_intro_thm(st, prelude, th_p, th_q))
  assert_true(lcc_concl_is(th, lcc_ok(prop_mk_and(st, prelude, p, q))))
  assert_true(lcc_hyps_are(th, [p, r, q]))
}

///|
test "Derivation.conjElimLeft: concludes p from p ∧ q with the same hypotheses" {
  let (st, prelude, p, q, _) = lcc_env()
  let pq = lcc_ok(prop_mk_and(st, prelude, p, q))
  let th = lcc_ok(
    logic_prop_and_elim_l_thm(st, prelude, lcc_ok(logic_assume(st, pq))),
  )
  assert_true(lcc_concl_is(th, p))
  assert_true(lcc_hyps_are(th, [pq]))
}

///|
test "Derivation.conjElimRight: concludes q from p ∧ q with the same hypotheses" {
  let (st, prelude, p, q, _) = lcc_env()
  let pq = lcc_ok(prop_mk_and(st, prelude, p, q))
  let th = lcc_ok(
    logic_prop_and_elim_r_thm(st, prelude, lcc_ok(logic_assume(st, pq))),
  )
  assert_true(lcc_concl_is(th, q))
  assert_true(lcc_hyps_are(th, [pq]))
}

///|
test "Derivation.conjElimLeft: premise A.concl = p ∧ q is enforced" {
  let (st, prelude, p, q, _) = lcc_env()
  let pq = lcc_ok(prop_mk_imp(st, prelude, p, q))
  let th = lcc_ok(logic_assume(st, pq))
  assert_true(logic_prop_and_elim_l_thm(st, prelude, th) is Err(_))
  assert_true(logic_prop_and_elim_r_thm(st, prelude, th) is Err(_))
  assert_true(
    logic_prop_and_elim_l_thm(st, prelude, lcc_ok(logic_assume(st, p)))
    is Err(_),
  )
}

///|
test "Derivation.impIntro: concludes p ⇒ c and removes p from the hypotheses" {
  let (st, prelude, p, q, r) = lcc_env()
  // A = {p, r} ⊢ q.
  let th_a = lcc_ok(
    logic_add_assum(
      st,
      p,
      lcc_ok(logic_add_assum(st, r, lcc_ok(logic_assume(st, q)))),
    ),
  )
  let th = lcc_ok(logic_prop_imp_intro_thm(st, prelude, p, th_a))
  assert_true(lcc_concl_is(th, lcc_ok(prop_mk_imp(st, prelude, p, q))))
  assert_true(lcc_hyps_are(th, [q, r]))
}

///|
test "Derivation.impIntro: p need not be a hypothesis" {
  let (st, prelude, p, q, _) = lcc_env()
  let th = lcc_ok(
    logic_prop_imp_intro_thm(st, prelude, p, lcc_ok(logic_assume(st, q))),
  )
  assert_true(lcc_concl_is(th, lcc_ok(prop_mk_imp(st, prelude, p, q))))
  assert_true(lcc_hyps_are(th, [q]))
}

///|
test "Derivation.impIntro: premise p : bool is enforced" {
  let (st, prelude, _, q, _) = lcc_env()
  let x = mk_var("x", mk_tyvar("A"))
  assert_true(
    logic_prop_imp_intro_thm(st, prelude, x, lcc_ok(logic_assume(st, q)))
    is Err(_),
  )
}

///|
test "Derivation.impElim: concludes q over the union of hypotheses" {
  let (st, prelude, p, q, r) = lcc_env()
  let pq = lcc_ok(prop_mk_imp(st, prelude, p, q))
  let th_p = lcc_ok(logic_add_assum(st, r, lcc_ok(logic_assume(st, p))))
  let th = lcc_ok(
    logic_prop_imp_elim_thm(st, prelude, lcc_ok(logic_assume(st, pq)), th_p),
  )
  assert_true(lcc_concl_is(th, q))
  assert_true(lcc_hyps_are(th, [pq, p, r]))
}

///|
test "Derivation.impElim: premises hA and hB are enforced" {
  let (st, prelude, p, q, r) = lcc_env()
  let th_pq = lcc_ok(logic_assume(st, lcc_ok(prop_mk_imp(st, prelude, p, q))))
  let th_r = lcc_ok(logic_assume(st, r))
  assert_true(logic_prop_imp_elim_thm(st, prelude, th_pq, th_r) is Err(_))
  let th_p = lcc_ok(logic_assume(st, p))
  assert_true(logic_prop_imp_elim_thm(st, prelude, th_p, th_p) is Err(_))
}
