///|
fn[T, E] expect_ok_positive(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn terms_match(lhs : Term, rhs : Term) -> Bool {
  term_logical_eq(lhs, rhs) || term_alpha_eq(lhs, rhs)
}

///|
fn normalized_term(state : KernelState, term : Term) -> Term {
  match logic_beta_nf_bool_term_deep(state, term) {
    Ok(v) => v
    Err(_) => term
  }
}

///|
fn concl_heads_match(state : KernelState, lhs : Term, rhs : Term) -> Bool {
  let lhs_nf = normalized_term(state, lhs)
  let rhs_nf = normalized_term(state, rhs)
  terms_match(lhs_nf, rhs_nf)
}

///|
fn concl_compat_or_tail(
  state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Bool {
  if terms_match(lhs, rhs) {
    true
  } else {
    let lhs_nf = normalized_term(state, lhs)
    let rhs_nf = normalized_term(state, rhs)
    if terms_match(lhs_nf, rhs_nf) {
      true
    } else {
      match
        (
          prop_dest_or(state, prelude, lhs_nf),
          prop_dest_or(state, prelude, rhs_nf),
        ) {
        (Some((ll, lr)), Some((rl, rr))) =>
          concl_heads_match(state, ll, rl) && concl_heads_match(state, lr, rr)
        _ => false
      }
    }
  }
}

///|
fn concls_match(state : KernelState, expected : Term, actual : Term) -> Bool {
  let prelude = default_prop_prelude()
  if terms_match(expected, actual) {
    true
  } else {
    let expected_nf = normalized_term(state, expected)
    let actual_nf = normalized_term(state, actual)
    if terms_match(expected_nf, actual_nf) {
      true
    } else {
      match
        (
          prop_dest_imp(state, prelude, expected_nf),
          prop_dest_imp(state, prelude, actual_nf),
        ) {
        (Some((ea, eb)), Some((aa, ab))) =>
          concl_heads_match(state, ea, aa) &&
          concl_compat_or_tail(state, prelude, eb, ab)
        _ => false
      }
    }
  }
}

///|
fn hyps_match(expected : Array[Term], actual : Array[Term]) -> Bool {
  if expected.length() != actual.length() {
    return false
  }
  let used : Array[Bool] = []
  let mut i = 0
  while i < actual.length() {
    used.push(false)
    i = i + 1
  }
  for h in expected {
    let mut j = 0
    let mut matched = false
    while j < actual.length() {
      if !used[j] && terms_match(h, actual[j]) {
        used[j] = true
        matched = true
        break
      }
      j = j + 1
    }
    if !matched {
      return false
    }
  }
  true
}

///|
fn build_bool_state(const_names : Array[String]) -> KernelState {
  let mut st = empty_kernel_state()
  for name in const_names {
    st = expect_ok_positive(ks_add_const(st, name, bool_ty()))
  }
  st
}

///|
enum PositiveCaseCheckResult {
  Pass
  ProofFailed
  ExpectedGoalFailed
  HypothesisDrift
  ConclusionDrift
}

///|
fn check_result_label(result : PositiveCaseCheckResult) -> String {
  match result {
    Pass => "pass"
    ProofFailed => "proof_failed"
    ExpectedGoalFailed => "expected_goal_failed"
    HypothesisDrift => "hypothesis_drift"
    ConclusionDrift => "conclusion_drift"
  }
}

///|
fn run_positive_corpus_case(
  case : PositiveCorpusCase,
) -> PositiveCaseCheckResult {
  let st0 = build_bool_state(case.const_names)
  let (st_out, th) = match
    prove_theorem_script(st0, case.script, default_prover_options()) {
    Ok(v) => v
    Err(_) => return ProofFailed
  }
  let expected_goal = match parse_goal(st_out, case.expected_goal) {
    Ok(v) => v
    Err(_) => return ExpectedGoalFailed
  }
  let actual_hyps = match thm_hyps(th) {
    Ok(v) => v
    Err(_) => return ProofFailed
  }
  let actual_concl = match thm_concl(th) {
    Ok(v) => v
    Err(_) => return ProofFailed
  }
  if !hyps_match(goal_hyps(expected_goal), actual_hyps) {
    return HypothesisDrift
  }
  if !concls_match(st_out, goal_concl(expected_goal), actual_concl) {
    return ConclusionDrift
  }
  Pass
}

///|
fn case_ids_are_unique(cases : Array[PositiveCorpusCase]) -> Bool {
  let seen : Array[String] = []
  for case in cases {
    if seen.contains(case.case_id) {
      return false
    }
    seen.push(case.case_id)
  }
  true
}

///|
fn cases_cover_catalog(
  cases : Array[PositiveCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) { catalog_label(case.catalog_class) == label })
}

///|
fn cases_cover_capability(
  cases : Array[PositiveCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) { capability_label(case.capability) == label })
}

///|
fn cases_cover_layout(
  cases : Array[PositiveCorpusCase],
  label : String,
) -> Bool {
  cases.any(fn(case) { script_layout_label(case.layout) == label })
}

///|
fn cases_cover_id(cases : Array[PositiveCorpusCase], case_id : String) -> Bool {
  cases.any(fn(case) { case.case_id == case_id })
}

///|
test "prove_theorem_script canonical positive corpus remains green" {
  let cases = positive_corpus_cases()
  for case in cases {
    let result = run_positive_corpus_case(case)
    assert_true(
      result is Pass,
      msg="positive corpus case `" +
        case.case_id +
        "` failed with `" +
        check_result_label(result) +
        "`",
    )
  }
}

///|
test "prove_theorem_script canonical positive corpus covers current classes" {
  let cases = positive_corpus_cases()
  assert_true(case_ids_are_unique(cases))
  assert_true(cases_cover_catalog(cases, "local_fact"))
  assert_true(cases_cover_catalog(cases, "direct_close"))
  assert_true(cases_cover_catalog(cases, "implication_backed"))
  assert_true(cases_cover_catalog(cases, "context_derived"))
  assert_true(cases_cover_catalog(cases, "structural_only"))
  assert_true(cases_cover_capability(cases, "intro_exact"))
  assert_true(cases_cover_capability(cases, "assumption"))
  assert_true(cases_cover_capability(cases, "exact_named_direct_close"))
  assert_true(cases_cover_capability(cases, "exact_context_derived"))
  assert_true(cases_cover_capability(cases, "apply_local_imp"))
  assert_true(cases_cover_capability(cases, "apply_named_imp"))
  assert_true(cases_cover_capability(cases, "split"))
  assert_true(cases_cover_capability(cases, "left"))
  assert_true(cases_cover_capability(cases, "right"))
  assert_true(cases_cover_capability(cases, "mixed"))
  assert_true(cases_cover_layout(cases, "inline_sequential"))
  assert_true(cases_cover_layout(cases, "block_sequential"))
  assert_true(cases_cover_id(cases, "pos_exact_and_intro"))
  assert_true(cases_cover_id(cases, "pos_exact_imp_elim"))
  assert_true(cases_cover_id(cases, "pos_exact_eq_refl"))
  assert_true(cases_cover_id(cases, "pos_exact_eq_sym"))
  assert_true(cases_cover_id(cases, "pos_exact_eq_mp"))
  assert_true(cases_cover_id(cases, "pos_apply_eq_sym"))
  assert_true(cases_cover_id(cases, "pos_block_exact_truth"))
  assert_true(cases_cover_id(cases, "pos_block_apply_or_intro_l"))
}
