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
