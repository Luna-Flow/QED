///|
fn[T, E] expect_ok_prop_ref(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn setup_prop_ref_env() -> (KernelState, PropPrelude, Term, Term, Term) {
  let prelude = default_prop_prelude()
  let st = expect_ok_prop_ref(install_prop_prelude(empty_kernel_state()))
  let p = mk_var("P", bool_ty())
  let q = mk_var("Q", bool_ty())
  let r = mk_var("R", bool_ty())
  (st, prelude, p, q, r)
}

///|
test "prop theorem catalog publishes shipped theorem names and classes" {
  assert_eq(logic_prop_theorem_count(), 13)

  let imp_refl = match logic_prop_theorem_entry("imp_refl") {
    Some(v) => v
    None => panic()
  }
  assert_eq(imp_refl.premise_count, 0)
  assert_true(imp_refl.exact_class is Some(DirectClose))
  assert_true(imp_refl.apply_class is None)

  let and_intro = match logic_prop_theorem_entry("and_intro") {
    Some(v) => v
    None => panic()
  }
  assert_eq(and_intro.premise_count, 2)
  assert_true(and_intro.exact_class is Some(ContextDerived))
  assert_true(and_intro.apply_class is None)

  let or_intro_l = match logic_prop_theorem_entry("or_intro_l") {
    Some(v) => v
    None => panic()
  }
  assert_eq(or_intro_l.premise_count, 1)
  assert_true(or_intro_l.exact_class is None)
  assert_true(or_intro_l.apply_class is Some(ImplicationBacked))

  let imp_elim = match logic_prop_theorem_entry("imp_elim") {
    Some(v) => v
    None => panic()
  }
  assert_eq(imp_elim.premise_count, 2)
  assert_true(imp_elim.exact_class is Some(ContextDerived))
  assert_true(imp_elim.apply_class is None)

  let eq_refl = match logic_prop_theorem_entry("eq_refl") {
    Some(v) => v
    None => panic()
  }
  assert_eq(eq_refl.premise_count, 0)
  assert_true(eq_refl.exact_class is Some(DirectClose))
  assert_true(eq_refl.apply_class is None)

  let eq_sym = match logic_prop_theorem_entry("eq_sym") {
    Some(v) => v
    None => panic()
  }
  assert_eq(eq_sym.premise_count, 1)
  assert_true(eq_sym.exact_class is Some(ContextDerived))
  assert_true(eq_sym.apply_class is Some(ImplicationBacked))

  let eq_mp = match logic_prop_theorem_entry("eq_mp") {
    Some(v) => v
    None => panic()
  }
  assert_eq(eq_mp.premise_count, 2)
  assert_true(eq_mp.exact_class is Some(ContextDerived))
  assert_true(eq_mp.apply_class is None)

  let first = match logic_prop_theorem_at(0) {
    Some(v) => v
    None => panic()
  }
  assert_eq(first.name, "imp_refl")
  assert_true(logic_prop_theorem_at(13) is None)
  assert_true(logic_prop_theorem_entry("missing") is None)
}

///|
test "exact witness resolver prefers local hypothesis over theorem names" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  let locals : Array[(String, Term)] = [("imp_refl", p)]
  match
    logic_prop_resolve_exact_witness(st, prelude, locals, [p], p, "imp_refl") {
    Some(ExactWitnessApplicable(ExactLocalHyp(name, t))) => {
      assert_eq(name, "imp_refl")
      assert_true(term_alpha_eq(t, p))
    }
    _ => panic()
  }
}

///|
test "exact witness resolver does not fall through past an unavailable local witness" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  let imp_pp = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, p))
  let locals : Array[(String, Term)] = [("imp_refl", p)]
  assert_true(
    logic_prop_resolve_exact_witness(
      st,
      prelude,
      locals,
      [p],
      imp_pp,
      "imp_refl",
    )
    is Some(ExactWitnessKnownButUnavailable),
  )
}

///|
test "exact witness resolver returns direct and context theorem witnesses" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let imp_pp = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, p))
  let and_pq = expect_ok_prop_ref(prop_mk_and(st, prelude, p, q))

  match
    logic_prop_resolve_exact_witness(st, prelude, [], [], imp_pp, "imp_refl") {
    Some(ExactWitnessApplicable(ExactDirectTheorem(name, th))) => {
      assert_eq(name, "imp_refl")
      assert_true(thm_concl(th) is Ok(_))
    }
    _ => panic()
  }

  match
    logic_prop_resolve_exact_witness(st, prelude, [], [and_pq], p, "and_elim_l") {
    Some(ExactWitnessApplicable(ExactContextTheorem(name, th, supports))) => {
      assert_eq(name, "and_elim_l")
      assert_eq(supports.length(), 1)
      assert_true(term_alpha_eq(supports[0], and_pq))
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(term_alpha_eq(concl, p))
    }
    _ => panic()
  }
}

///|
test "prop refs resolve local facts before named theorems" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  let imp_pp = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, p))
  let locals : Array[(String, Term)] = [("imp_refl", p)]
  let pool : Array[Term] = [p]
  match logic_prop_resolve_ref(st, prelude, locals, pool, imp_pp, "imp_refl") {
    Some(LocalFact(t)) => assert_true(term_alpha_eq(t, p))
    _ => panic()
  }
}

///|
test "named imp_refl only resolves on reflexive implication goals" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let imp_pp = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, p))
  let imp_pq = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, q))
  assert_true(
    logic_prop_named_theorem(st, prelude, "imp_refl", imp_pp) is Some(_),
  )
  assert_true(logic_prop_named_theorem(st, prelude, "imp_refl", imp_pq) is None)
}

///|
test "context theorem resolution picks first matching conjunction owner from pool order" {
  let (st, prelude, p, q, r) = setup_prop_ref_env()
  let owner1 = expect_ok_prop_ref(prop_mk_and(st, prelude, p, q))
  let owner2 = expect_ok_prop_ref(prop_mk_and(st, prelude, p, r))
  let pool : Array[Term] = [owner1, owner2]
  match logic_prop_context_theorem(st, prelude, "and_elim_l", pool, p) {
    Some((th, antecedent)) => {
      assert_true(term_alpha_eq(antecedent, owner1))
      match thm_concl(th) {
        Ok(concl) => assert_true(term_alpha_eq(concl, p))
        Err(_) => panic()
      }
      match thm_hyps(th) {
        Ok(hs) => {
          assert_eq(hs.length(), 1)
          assert_true(term_alpha_eq(hs[0], owner1))
        }
        Err(_) => panic()
      }
    }
    None => panic()
  }
}

///|
test "context apply theorem resolution for or intro only resolves on disjunction goals" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let or_pq = expect_ok_prop_ref(prop_mk_or(st, prelude, p, q))
  assert_true(
    logic_prop_context_apply_theorem(st, prelude, "or_intro_l", [], or_pq)
    is Some((_, _)),
  )
  assert_true(
    logic_prop_context_apply_theorem(st, prelude, "or_intro_l", [], p) is None,
  )
}

///|
test "named truth theorem only resolves on T goals" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  let t_term = expect_ok_prop_ref(ks_mk_const(st, prelude.truth_name))
  assert_true(logic_prop_named_theorem(st, prelude, "truth", t_term) is Some(_))
  assert_true(logic_prop_named_theorem(st, prelude, "truth", p) is None)
}

///|
test "exact resolver marks known theorem names unavailable when shape or context is missing" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let or_pq = expect_ok_prop_ref(prop_mk_or(st, prelude, p, q))
  let eq_pq = expect_ok_prop_ref(mk_eq(p, q))
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [], or_pq, "or_intro_l")
    is Some(ExactKnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [], eq_pq, "eq_sym")
    is Some(ExactKnownButUnavailable),
  )
}

///|
test "exact resolver distinguishes known-unavailable names from unknown names" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let imp_pq = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, q))
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [], imp_pq, "imp_refl")
    is Some(ExactKnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [], imp_pq, "missing") is None,
  )
}

///|
test "exact resolver supports and_intro theorem name" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let and_pq = expect_ok_prop_ref(prop_mk_and(st, prelude, p, q))

  match
    logic_prop_resolve_exact_theorem(st, prelude, [p, q], and_pq, "and_intro") {
    Some(ExactApplicable(th)) => {
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(
        term_alpha_eq(concl, and_pq) || term_logical_eq(concl, and_pq),
      )
      let hs = expect_ok_prop_ref(thm_hyps(th))
      assert_eq(hs.length(), 2)
      assert_true(hs.any(fn(h) { term_alpha_eq(h, p) }))
      assert_true(hs.any(fn(h) { term_alpha_eq(h, q) }))
    }
    _ => panic()
  }
}

///|
test "exact resolver supports imp_elim and equality theorem names" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let imp_pq = expect_ok_prop_ref(prop_mk_imp(st, prelude, p, q))
  let eq_pp = expect_ok_prop_ref(mk_eq(p, p))
  let eq_pq = expect_ok_prop_ref(mk_eq(p, q))
  let eq_qp = expect_ok_prop_ref(mk_eq(q, p))

  match
    logic_prop_resolve_exact_theorem(st, prelude, [imp_pq, p], q, "imp_elim") {
    Some(ExactApplicable(th)) => {
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(term_alpha_eq(concl, q))
    }
    _ => panic()
  }

  match logic_prop_resolve_exact_theorem(st, prelude, [], eq_pp, "eq_refl") {
    Some(ExactApplicable(th)) => {
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(term_alpha_eq(concl, eq_pp) || term_logical_eq(concl, eq_pp))
    }
    _ => panic()
  }

  match
    logic_prop_resolve_exact_theorem(st, prelude, [eq_qp], eq_pq, "eq_sym") {
    Some(ExactApplicable(th)) => {
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(term_alpha_eq(concl, eq_pq) || term_logical_eq(concl, eq_pq))
    }
    _ => panic()
  }

  match logic_prop_resolve_exact_theorem(st, prelude, [eq_pq, p], q, "eq_mp") {
    Some(ExactApplicable(th)) => {
      let concl = expect_ok_prop_ref(thm_concl(th))
      assert_true(term_alpha_eq(concl, q))
    }
    _ => panic()
  }
}

///|
test "apply resolver returns implication-backed theorem when available" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let or_pq = expect_ok_prop_ref(prop_mk_or(st, prelude, p, q))
  match logic_prop_resolve_apply_theorem(st, prelude, [], or_pq, "or_intro_l") {
    Some(Applicable(th, antecedent)) => {
      assert_true(
        term_logical_eq(antecedent, p) || term_alpha_eq(antecedent, p),
      )
      assert_true(thm_concl(th) is Ok(_))
    }
    _ => panic()
  }
}

///|
test "apply resolver supports eq_sym and marks unavailable names honestly" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let t_term = expect_ok_prop_ref(ks_mk_const(st, prelude.truth_name))
  let eq_pq = expect_ok_prop_ref(mk_eq(p, q))
  let eq_qp = expect_ok_prop_ref(mk_eq(q, p))

  match logic_prop_resolve_apply_theorem(st, prelude, [], eq_pq, "eq_sym") {
    Some(Applicable(th, antecedent)) => {
      assert_true(
        term_alpha_eq(antecedent, eq_qp) || term_logical_eq(antecedent, eq_qp),
      )
      assert_true(thm_concl(th) is Ok(_))
    }
    _ => panic()
  }

  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [], t_term, "truth")
    is Some(KnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [], q, "and_intro")
    is Some(KnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [], q, "imp_elim")
    is Some(KnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [], q, "eq_mp")
    is Some(KnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [], q, "missing") is None,
  )
}

///|
test "apply resolver marks implication-backed names unavailable on bad goal shape" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [p], p, "and_elim_l")
    is Some(KnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_apply_theorem(st, prelude, [p], p, "eq_sym")
    is Some(KnownButUnavailable),
  )
}

///|
test "exact resolver marks known theorem names unavailable on missing context" {
  let (st, prelude, p, _, _) = setup_prop_ref_env()
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [p], p, "and_elim_l")
    is Some(ExactKnownButUnavailable),
  )
  assert_true(
    logic_prop_resolve_exact_theorem(st, prelude, [p], p, "eq_mp")
    is Some(ExactKnownButUnavailable),
  )
}

///|
test "context theorem resolution supports not_elim and ex_falso" {
  let (st, prelude, p, q, _) = setup_prop_ref_env()
  let false_term = expect_ok_prop_ref(ks_mk_const(st, prelude.false_name))
  let not_p = expect_ok_prop_ref(prop_mk_not(st, prelude, p))
  let pool_not : Array[Term] = [not_p, p]
  let pool_false : Array[Term] = [false_term]
  match
    logic_prop_context_theorem(st, prelude, "not_elim", pool_not, false_term) {
    Some((th_not_elim, antecedent_not_elim)) => {
      assert_true(term_alpha_eq(antecedent_not_elim, false_term))
      match thm_concl(th_not_elim) {
        Ok(concl) => assert_true(term_alpha_eq(concl, false_term))
        Err(_) => panic()
      }
    }
    None => panic()
  }
  match logic_prop_context_theorem(st, prelude, "ex_falso", pool_false, q) {
    Some((th_ex_falso, antecedent_ex_falso)) => {
      assert_true(term_alpha_eq(antecedent_ex_falso, false_term))
      match thm_concl(th_ex_falso) {
        Ok(concl) => assert_true(term_alpha_eq(concl, q))
        Err(_) => panic()
      }
      match thm_hyps(th_ex_falso) {
        Ok(hs) => {
          assert_eq(hs.length(), 1)
          assert_true(term_alpha_eq(hs[0], false_term))
        }
        Err(_) => panic()
      }
    }
    None => panic()
  }
}
