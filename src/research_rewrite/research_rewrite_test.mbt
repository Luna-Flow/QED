///|
fn[T, E] expect_ok_research(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn installed_prop_state() -> (KernelState, PropPrelude) {
  let prelude = default_prop_prelude()
  let st = expect_ok_research(install_prop_prelude(empty_kernel_state()))
  (st, prelude)
}

///|
fn named_and_term(
  state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Term {
  let and_c = expect_ok_research(ks_mk_const(state, prelude.and_name))
  mk_comb(mk_comb(and_c, lhs), rhs)
}

///|
fn has_step_named(steps : Array[ReplayStepKind], target : String) -> Bool {
  steps.any(fn(step) { research_step_name(step) == target })
}

///|
test "research rewrite uses local equality on conclusion subterm" {
  let (st, prelude) = installed_prop_state()
  let a = mk_tyvar("A")
  let pred = mk_var("pred", fun_ty(a, bool_ty()))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let concl = mk_comb(pred, x)
  let eq_xy = expect_ok_research(mk_eq(x, y))
  let req = research_rewrite_request(
    research_local_equality("hxy"),
    research_left_to_right(),
    [research_site_comb_arg()],
  )
  let locals : Array[(String, Term)] = [("hxy", eq_xy)]
  match research_rewrite_term_concl(st, prelude, locals, concl, req) {
    Rewritten(after, obligation) => {
      assert_true(term_alpha_eq(after, mk_comb(pred, y)))
      assert_eq(obligation.segments.length(), 1)
      assert_true(
        has_step_named(obligation.segments[0].steps, "ResolveWitness"),
      )
      assert_true(has_step_named(obligation.segments[0].steps, "Congruence"))
      assert_true(
        research_validate_replay_obligation(st, prelude, locals, obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }
}

///|
test "research rewrite supports explicit theorem symmetry" {
  let (st, prelude) = installed_prop_state()
  let a = mk_tyvar("A")
  let pred = mk_var("pred", fun_ty(a, bool_ty()))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let concl = mk_comb(pred, y)
  let th_xy = expect_ok_research(
    logic_assume(st, expect_ok_research(mk_eq(x, y))),
  )
  let req = research_rewrite_request(
    research_explicit_theorem(th_xy),
    research_right_to_left(),
    [research_site_comb_arg()],
  )
  let locals : Array[(String, Term)] = []
  match research_rewrite_term_concl(st, prelude, locals, concl, req) {
    Rewritten(after, obligation) => {
      assert_true(term_alpha_eq(after, mk_comb(pred, x)))
      assert_true(has_step_named(obligation.segments[0].steps, "Symmetry"))
      assert_true(
        research_validate_replay_obligation(st, prelude, locals, obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }
}

///|
test "research rewrite canonical unfold uses named connector head" {
  let (st, prelude) = installed_prop_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let concl = named_and_term(st, prelude, p, q)
  let expected = expect_ok_research(prop_mk_and(st, prelude, p, q))
  let req = research_rewrite_request(
    research_canonical_unfold_and(),
    research_left_to_right(),
    [],
  )
  let locals : Array[(String, Term)] = []
  match research_rewrite_term_concl(st, prelude, locals, concl, req) {
    Rewritten(after, obligation) => {
      assert_true(term_alpha_eq(after, expected))
      assert_true(has_step_named(obligation.segments[0].steps, "Unfold"))
      assert_true(has_step_named(obligation.segments[0].steps, "BetaNormalize"))
      assert_true(
        research_validate_replay_obligation(st, prelude, locals, obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }
}

///|
test "research rewrite beta-normalizes a root redex" {
  let (st, prelude) = installed_prop_state()
  let p = mk_var("p", bool_ty())
  let x = mk_var("x", bool_ty())
  let concl = mk_comb(mk_abs(x, x), p)
  let req = research_rewrite_request(
    research_beta_normalization(),
    research_left_to_right(),
    [],
  )
  let locals : Array[(String, Term)] = []
  match research_rewrite_term_concl(st, prelude, locals, concl, req) {
    Rewritten(after, obligation) => {
      assert_true(term_alpha_eq(after, p))
      assert_true(has_step_named(obligation.segments[0].steps, "BetaNormalize"))
      assert_true(
        research_validate_replay_obligation(st, prelude, locals, obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }
}

///|
test "research rewrite rejects missing local equality" {
  let (st, prelude) = installed_prop_state()
  let a = mk_tyvar("A")
  let pred = mk_var("pred", fun_ty(a, bool_ty()))
  let x = mk_var("x", a)
  let concl = mk_comb(pred, x)
  let req = research_rewrite_request(
    research_local_equality("missing"),
    research_left_to_right(),
    [research_site_comb_arg()],
  )
  assert_true(
    research_rewrite_term_concl(st, prelude, [], concl, req) is HonestFailure(_),
  )
}

///|
test "research rewrite rejects non-equality theorem witness" {
  let (st, prelude) = installed_prop_state()
  let p = mk_var("p", bool_ty())
  let th_p = expect_ok_research(logic_assume(st, p))
  let req = research_rewrite_request(
    research_explicit_theorem(th_p),
    research_left_to_right(),
    [],
  )
  assert_true(
    research_rewrite_term_concl(st, prelude, [], p, req) is HonestFailure(_),
  )
}

///|
test "research rewrite rejects focus mismatch and abs-body requests" {
  let (st, prelude) = installed_prop_state()
  let a = mk_tyvar("A")
  let pred = mk_var("pred", fun_ty(a, bool_ty()))
  let pred_lam = mk_var("pred_lam", fun_ty(fun_ty(a, a), bool_ty()))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let concl = mk_comb(pred, x)
  let req_bad = research_rewrite_request(
    research_local_equality("hxy"),
    research_left_to_right(),
    [],
  )
  let locals : Array[(String, Term)] = [
    ("hxy", expect_ok_research(mk_eq(x, y))),
  ]
  assert_true(
    research_rewrite_term_concl(st, prelude, locals, concl, req_bad)
    is HonestFailure(_),
  )

  let lam = mk_abs(x, x)
  let concl_abs = mk_comb(pred_lam, lam)
  let req_abs = research_rewrite_request(
    research_beta_normalization(),
    research_left_to_right(),
    [research_site_comb_arg(), research_site_abs_body()],
  )
  assert_true(
    research_rewrite_term_concl(st, prelude, [], concl_abs, req_abs)
    is HonestFailure(_),
  )
}

///|
test "research validate obligation rejects tampered after-conclusion" {
  let (st, prelude) = installed_prop_state()
  let p = mk_var("p", bool_ty())
  let x = mk_var("x", bool_ty())
  let concl = mk_comb(mk_abs(x, x), p)
  let req = research_rewrite_request(
    research_beta_normalization(),
    research_left_to_right(),
    [],
  )
  match research_rewrite_term_concl(st, prelude, [], concl, req) {
    Rewritten(_, obligation) => {
      let bad = research_replay_obligation(
        obligation.before_concl,
        obligation.before_concl,
        obligation.segments,
      )
      assert_true(
        research_validate_replay_obligation(st, prelude, [], bad) is Err(_),
      )
    }
    _ => panic()
  }
}

///|
test "research simplify composes inner beta and local equality rewrites" {
  let (st, prelude) = installed_prop_state()
  let a = mk_tyvar("A")
  let pred = mk_var("pred", fun_ty(a, bool_ty()))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let u = mk_var("u", a)
  let redex = mk_comb(mk_abs(u, u), x)
  let concl = mk_comb(pred, redex)
  let locals : Array[(String, Term)] = [
    ("hxy", expect_ok_research(mk_eq(x, y))),
  ]
  let beta_req = research_rewrite_request(
    research_beta_normalization(),
    research_left_to_right(),
    [research_site_comb_arg()],
  )
  let eq_req = research_rewrite_request(
    research_local_equality("hxy"),
    research_left_to_right(),
    [research_site_comb_arg()],
  )
  let cfg = research_simplify_config(2, false, false, [beta_req, eq_req])
  match research_simplify_term_concl(st, prelude, locals, concl, cfg) {
    Rewritten(after, obligation) => {
      assert_true(term_alpha_eq(after, mk_comb(pred, y)))
      assert_eq(obligation.segments.length(), 2)
      assert_true(
        research_validate_replay_obligation(st, prelude, locals, obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }
}

///|
test "research simplify supports root unfold and step-limit failure" {
  let (st, prelude) = installed_prop_state()
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let concl = named_and_term(st, prelude, p, q)
  let cfg_ok = research_simplify_config(1, true, false, [])
  match research_simplify_term_concl(st, prelude, [], concl, cfg_ok) {
    Rewritten(after, obligation) => {
      let expected = expect_ok_research(prop_mk_and(st, prelude, p, q))
      assert_true(term_alpha_eq(after, expected))
      assert_true(
        research_validate_replay_obligation(st, prelude, [], obligation)
        is Ok(_),
      )
    }
    _ => panic()
  }

  let cfg_limit = research_simplify_config(0, true, false, [])
  assert_true(
    research_simplify_term_concl(st, prelude, [], concl, cfg_limit)
    is HonestFailure(_),
  )
}
