// Conformance tests for the quantifier constructors of `inductive Derivation`
// in formal_verification/QEDFV/HOL/Derivation.lean.
//
// Lean takes `Term.all` and `Term.ex` as primitive term formers; this package
// defines them over the prelude (prop_quant.mbt) and derives the rules. Each
// test is named `Derivation.<constructor>: ...` and checks the conclusion and
// hypotheses the constructor states, plus each of its premises. Lean's context
// weakening (`weakenSequent`) is the named side condition that the bound
// variable is not free in the hypotheses or the conclusion it must avoid.

///|
fn[T, E] lq_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn lq_env() -> (KernelState, PropPrelude) {
  (lq_ok(install_prop_prelude(empty_kernel_state())), default_prop_prelude())
}

///|
fn lq_concl_is(th : Thm, expected : Term) -> Bool {
  term_alpha_eq(lq_ok(thm_concl(th)), expected)
}

///|
/// Set equality of hypotheses modulo alpha-equivalence.
fn lq_hyps_are(th : Thm, expected : Array[Term]) -> Bool {
  let hyps = lq_ok(thm_hyps(th))
  hyps.all(h => expected.any(e => term_alpha_eq(h, e))) &&
  expected.all(e => hyps.any(h => term_alpha_eq(h, e)))
}

///|
fn lq_all(st : KernelState, pre : PropPrelude, x : Term, body : Term) -> Term {
  lq_ok(logic_quant_mk_all(st, pre, x, body))
}

///|
fn lq_ex(st : KernelState, pre : PropPrelude, x : Term, body : Term) -> Term {
  lq_ok(logic_quant_mk_ex(st, pre, x, body))
}

///|
fn lq_imp(st : KernelState, pre : PropPrelude, p : Term, q : Term) -> Term {
  lq_ok(prop_mk_imp(st, pre, p, q))
}

///|
test "logic_quant: the encodings round-trip and ∀ has the tactics' shape" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let pv = mk_var("P", fun_ty(a, bool_ty()))
  let body = mk_comb(pv, x)
  let all = lq_all(st, pre, x, body)
  let truth = lq_ok(ks_mk_const(st, prop_truth_name(pre)))
  assert_true(
    term_alpha_eq(all, lq_ok(mk_eq(mk_abs(x, body), mk_abs(x, truth)))),
  )
  let (x1, b1) = logic_quant_dest_all(st, pre, all).unwrap()
  assert_true(term_alpha_eq(mk_abs(x1, b1), mk_abs(x, body)))
  let ex = lq_ex(st, pre, x, body)
  let (x2, b2) = logic_quant_dest_ex(st, pre, ex).unwrap()
  assert_true(term_alpha_eq(mk_abs(x2, b2), mk_abs(x, body)))
  // ∃ is not a ∀ over the body, and a non-variable binder is rejected.
  assert_true(logic_quant_dest_ex(st, pre, all) is None)
  assert_true(
    logic_quant_mk_all(st, pre, body, mk_var("p", bool_ty())) is Err(_),
  )
  assert_true(logic_quant_mk_all(st, pre, x, x) is Err(_))
}

///|
test "logic_quant: the ∃ bound proposition avoids free names of the body" {
  let (st, pre) = lq_env()
  let x = mk_var("x", bool_ty())
  let q = mk_var("_q_ex", bool_ty())
  let ex = lq_ex(st, pre, x, q)
  let (_, body) = logic_quant_dest_ex(st, pre, ex).unwrap()
  assert_true(term_alpha_eq(body, q))
}

///|
test "Derivation.allIntro: concludes ∀x. φ with the same hypotheses" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let x_eq = lq_ok(mk_eq(x, x))
  let th = lq_ok(
    logic_quant_all_intro_thm(st, pre, x, lq_ok(logic_refl(st, x))),
  )
  assert_true(lq_concl_is(th, lq_all(st, pre, x, x_eq)))
  assert_true(lq_hyps_are(th, []))
  // Hypotheses are kept as they are, including T.
  let p = mk_var("p", bool_ty())
  let th_p = lq_ok(
    logic_quant_all_intro_thm(st, pre, x, lq_ok(logic_assume(st, p))),
  )
  assert_true(lq_concl_is(th_p, lq_all(st, pre, x, p)))
  assert_true(lq_hyps_are(th_p, [p]))
  let truth = lq_ok(ks_mk_const(st, prop_truth_name(pre)))
  let th_t = lq_ok(
    logic_quant_all_intro_thm(st, pre, x, lq_ok(logic_assume(st, truth))),
  )
  assert_true(lq_concl_is(th_t, lq_all(st, pre, x, truth)))
  assert_true(lq_hyps_are(th_t, [truth]))
}

///|
test "Derivation.allIntro: the premise is weakened, so x is not free in the hypotheses" {
  let (st, pre) = lq_env()
  let p = mk_var("p", bool_ty())
  let th = lq_ok(logic_assume(st, p))
  assert_true(logic_quant_all_intro_thm(st, pre, p, th) is Err(_))
  // A binder of the same name but another type would shadow the free `p` by
  // name; the kernel's named boundary rejects such terms, so this fails too.
  let p_a = mk_var("p", mk_tyvar("A"))
  assert_true(logic_quant_all_intro_thm(st, pre, p_a, th) is Err(_))
}

///|
test "Derivation.allElim: concludes φ[t/x] with the same hypotheses" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let t = mk_comb(mk_var("f", fun_ty(a, a)), mk_var("c", a))
  let p = mk_var("p", bool_ty())
  let th_all = lq_ok(
    logic_quant_all_intro_thm(
      st,
      pre,
      x,
      lq_ok(logic_add_assum(st, p, lq_ok(logic_refl(st, x)))),
    ),
  )
  let th = lq_ok(logic_quant_all_elim_thm(st, pre, t, th_all))
  assert_true(lq_concl_is(th, lq_ok(mk_eq(t, t))))
  assert_true(lq_hyps_are(th, [p]))
}

///|
test "Derivation.allElim: substitution avoids capture and reduces only the outer redex" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  // ∀x. (λy. x) = (λy. x), specialised to y, is (λz. y) = (λz. y).
  let k = mk_abs(y, x)
  let th_all = lq_ok(
    logic_quant_all_intro_thm(st, pre, x, lq_ok(logic_refl(st, k))),
  )
  let th = lq_ok(logic_quant_all_elim_thm(st, pre, y, th_all))
  let kz = mk_abs(z, y)
  assert_true(lq_concl_is(th, lq_ok(mk_eq(kz, kz))))
  let ky = mk_abs(y, y)
  assert_false(lq_concl_is(th, lq_ok(mk_eq(ky, ky))))
  // A redex inside φ stays: φ.substitute does not normalise.
  let redex = mk_comb(mk_abs(z, z), x)
  let th_all2 = lq_ok(
    logic_quant_all_intro_thm(st, pre, x, lq_ok(logic_refl(st, redex))),
  )
  let th2 = lq_ok(logic_quant_all_elim_thm(st, pre, y, th_all2))
  let redex_y = mk_comb(mk_abs(z, z), y)
  assert_true(lq_concl_is(th2, lq_ok(mk_eq(redex_y, redex_y))))
}

///|
test "Derivation.allElim: premise A.concl = ∀x. φ and the type of t are enforced" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let th_refl = lq_ok(logic_refl(st, x))
  assert_true(logic_quant_all_elim_thm(st, pre, x, th_refl) is Err(_))
  let th_all = lq_ok(logic_quant_all_intro_thm(st, pre, x, th_refl))
  assert_true(
    logic_quant_all_elim_thm(st, pre, mk_var("b", bool_ty()), th_all) is Err(_),
  )
}

///|
test "Derivation.exIntro: concludes ∃x. φ from φ[t/x] with the same hypotheses" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let pv = mk_var("P", fun_ty(a, bool_ty()))
  let c = mk_var("c", a)
  let body = mk_comb(pv, x)
  let pc = mk_comb(pv, c)
  let th = lq_ok(
    logic_quant_ex_intro_thm(st, pre, x, body, c, lq_ok(logic_assume(st, pc))),
  )
  assert_true(lq_concl_is(th, lq_ex(st, pre, x, body)))
  assert_true(lq_hyps_are(th, [pc]))
  // A hypothesis that uses the name of the bound proposition is kept.
  let q = mk_var("_q_ex", bool_ty())
  let th_q = lq_ok(
    logic_quant_ex_intro_thm(st, pre, x, q, c, lq_ok(logic_assume(st, q))),
  )
  assert_true(lq_concl_is(th_q, lq_ex(st, pre, x, q)))
  assert_true(lq_hyps_are(th_q, [q]))
}

///|
test "Derivation.exIntro: premise A.concl = φ[t/x] is enforced" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let pv = mk_var("P", fun_ty(a, bool_ty()))
  let c = mk_var("c", a)
  let d = mk_var("d", a)
  let th = lq_ok(logic_assume(st, mk_comb(pv, c)))
  assert_true(
    logic_quant_ex_intro_thm(st, pre, x, mk_comb(pv, x), d, th) is Err(_),
  )
}

///|
/// `{P c} ⊢ ∃x. P x`, the `A` of the exElim tests.
fn lq_ex_premise(
  st : KernelState,
  pre : PropPrelude,
) -> (Thm, Term, Term, Term) {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let pv = mk_var("P", fun_ty(a, bool_ty()))
  let pc = mk_comb(pv, mk_var("c", a))
  let th = lq_ok(
    logic_quant_ex_intro_thm(
      st,
      pre,
      x,
      mk_comb(pv, x),
      mk_var("c", a),
      lq_ok(logic_assume(st, pc)),
    ),
  )
  (th, pv, pc, mk_var("v", a))
}

///|
test "Derivation.exElim: concludes B over A.hyps ∪ B.hyps, discharging φ[v/x]" {
  let (st, pre) = lq_env()
  let (th_ex, pv, pc, v) = lq_ex_premise(st, pre)
  let q = mk_var("q", bool_ty())
  let y = mk_var("y", type_of(v).unwrap())
  // {∀y. P y ⇒ q, P v} ⊢ q
  let h = lq_all(st, pre, y, lq_imp(st, pre, mk_comb(pv, y), q))
  let pvv = mk_comb(pv, v)
  let th_b = lq_ok(
    logic_prop_imp_elim_thm(
      st,
      pre,
      lq_ok(logic_quant_all_elim_thm(st, pre, v, lq_ok(logic_assume(st, h)))),
      lq_ok(logic_assume(st, pvv)),
    ),
  )
  assert_true(lq_hyps_are(th_b, [h, pvv]))
  let th = lq_ok(logic_quant_ex_elim_thm(st, pre, th_ex, v, th_b))
  assert_true(lq_concl_is(th, q))
  assert_true(lq_hyps_are(th, [pc, h]))
}

///|
test "Derivation.exElim: premises A.concl = ∃x. φ and the weakening of B are enforced" {
  let (st, pre) = lq_env()
  let (th_ex, pv, _, v) = lq_ex_premise(st, pre)
  let pvv = mk_comb(pv, v)
  let q = mk_var("q", bool_ty())
  let th_ok = lq_ok(logic_add_assum(st, pvv, lq_ok(logic_assume(st, q))))
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, v, th_ok) is Ok(_))
  // A is not an existential.
  assert_true(
    logic_quant_ex_elim_thm(st, pre, lq_ok(logic_assume(st, q)), v, th_ok)
    is Err(_),
  )
  // v free in the conclusion B.
  let th_b_concl = lq_ok(logic_assume(st, pvv))
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, v, th_b_concl) is Err(_))
  // v free in another hypothesis of B.
  let r = mk_comb(mk_var("R", fun_ty(type_of(v).unwrap(), bool_ty())), v)
  let th_b_hyp = lq_ok(logic_add_assum(st, r, th_ok))
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, v, th_b_hyp) is Err(_))
  // v of another type than the bound variable.
  let v_bool = mk_var("v", bool_ty())
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, v_bool, th_ok) is Err(_))
  // A non-variable witness name.
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, pvv, th_ok) is Err(_))
}

///|
test "Derivation.exElim: v must not be free in ∃x. φ" {
  let (st, pre) = lq_env()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let v = mk_var("v", a)
  let rv = mk_var("R", fun_ty(a, fun_ty(a, bool_ty())))
  // {R v v} ⊢ ∃x. R x v
  let body = mk_comb(mk_comb(rv, x), v)
  let rvv = mk_comb(mk_comb(rv, v), v)
  let th_ex = lq_ok(
    logic_quant_ex_intro_thm(st, pre, x, body, v, lq_ok(logic_assume(st, rvv))),
  )
  // {R v v, q} ⊢ q would discharge R v v, which is not an instance of a fresh v.
  let q = mk_var("q", bool_ty())
  let th_b = lq_ok(logic_add_assum(st, rvv, lq_ok(logic_assume(st, q))))
  assert_true(logic_quant_ex_elim_thm(st, pre, th_ex, v, th_b) is Err(_))
}
