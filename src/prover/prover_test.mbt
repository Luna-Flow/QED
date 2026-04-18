///|

///|
fn[T, E] expect_ok_prover(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn expect_proved(result : ProverRunResult) -> ProverSuccess {
  match result {
    Proved(ok) => ok
    Failed(_) => panic()
    Unfinished(_) => panic()
  }
}

///|
fn expect_failed(result : ProverRunResult) -> ProverFailure {
  match result {
    Proved(_) => panic()
    Failed(err) => err
    Unfinished(_) => panic()
  }
}

///|
fn expect_unfinished(result : ProverRunResult) -> ProverUnfinished {
  match result {
    Proved(_) => panic()
    Failed(_) => panic()
    Unfinished(unfinished) => unfinished
  }
}

///|
fn expect_diag_failed(
  res : Result[(KernelState, Thm), ProverFailure],
) -> ProverFailure {
  match res {
    Err(err) => err
    Ok(_) => panic()
  }
}

///|
fn unfinished_fixture_goal() -> Goal {
  let st = expect_ok_prover(install_prop_prelude(empty_kernel_state()))
  let parsed = match parse_goal(st, "T ⊢ T") {
    Ok(v) => v
    Err(_) => panic()
  }
  mk_goal(parsed_goal_hyps(parsed), parsed_goal_concl(parsed))
}

///|
test "prover_unfinished helper preserves stable payload fields" {
  let goal = unfinished_fixture_goal()
  let goal_span = source_span(11, 16)
  let step_span = source_span(27, 31)
  let result = prover_unfinished(
    "holey",
    Some("T ⊢ T"),
    Some(goal_span),
    Some(3),
    [2, 1],
    Some(step_span),
    Some("_"),
    goal,
    [prover_local_hyp("h", goal_hyps(goal)[0])],
    Some("h1"),
    "proof contains an unfinished hole",
    Some(27),
  )
  let unfinished = expect_unfinished(result)
  assert_eq(unfinished.theorem_name, "holey")
  assert_eq(unfinished.goal_src, Some("T ⊢ T"))
  match unfinished.goal_span {
    Some(span) => {
      assert_eq(span.start_offset, goal_span.start_offset)
      assert_eq(span.end_offset, goal_span.end_offset)
    }
    None => panic()
  }
  assert_eq(unfinished.step_index, Some(3))
  assert_eq(unfinished.branch_path, [2, 1])
  match unfinished.step_span {
    Some(span) => {
      assert_eq(span.start_offset, step_span.start_offset)
      assert_eq(span.end_offset, step_span.end_offset)
    }
    None => panic()
  }
  assert_eq(unfinished.step_src, Some("_"))
  assert_eq(goal_hyps(unfinished.current_goal).length(), 1)
  assert_true(
    term_alpha_eq(goal_concl(unfinished.current_goal), goal_hyps(goal)[0]),
  )
  assert_eq(unfinished.local_hyps.length(), 1)
  assert_eq(unfinished.local_hyps[0].name, "h")
  assert_true(term_alpha_eq(unfinished.local_hyps[0].term, goal_hyps(goal)[0]))
  assert_eq(unfinished.hole_name, Some("h1"))
  assert_eq(unfinished.detail, "proof contains an unfinished hole")
  assert_eq(unfinished.raw_offset, Some(27))
}

///|
test "prover_unfinished helper keeps optional fields nullable" {
  let goal = unfinished_fixture_goal()
  let unfinished = expect_unfinished(
    prover_unfinished(
      "holey",
      None,
      None,
      None,
      [],
      None,
      None,
      goal,
      [],
      None,
      "todo",
      None,
    ),
  )
  assert_eq(unfinished.theorem_name, "holey")
  assert_true(unfinished.goal_src is None)
  assert_true(unfinished.goal_span is None)
  assert_true(unfinished.step_index is None)
  assert_eq(unfinished.branch_path, [])
  assert_true(unfinished.step_span is None)
  assert_true(unfinished.step_src is None)
  assert_eq(goal_hyps(unfinished.current_goal).length(), 1)
  assert_eq(unfinished.local_hyps.length(), 0)
  assert_true(unfinished.hole_name is None)
  assert_eq(unfinished.detail, "todo")
  assert_true(unfinished.raw_offset is None)
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
test "prove_theorem_script accepts theorem header binders" {
  let script = "theorem t (P : bool) : ⊢ P -> P := by intro h; exact h"
  let (_st, th) = expect_ok_prover(
    prove_theorem_script(empty_kernel_state(), script, default_prover_options()),
  )
  let st_pre = expect_ok_prover(install_prop_prelude(empty_kernel_state()))
  let prelude = default_prop_prelude()
  let p = mk_var("P", bool_ty())
  let target = expect_ok_prover(prop_mk_imp(st_pre, prelude, p, p))
  let concl = expect_ok_prover(thm_concl(th))
  assert_true(term_logical_eq(concl, target))
}

///|
test "prove_theorem_script keeps theorem header binders above same-named constants" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let script = "theorem t (P : bool) : ⊢ P -> P := by exact imp_refl"
  let (st_out, th) = expect_ok_prover(
    prove_theorem_script(st0, script, default_prover_options()),
  )
  let prelude = default_prop_prelude()
  let local_p = mk_var("P", bool_ty())
  let local_target = expect_ok_prover(
    prop_mk_imp(st_out, prelude, local_p, local_p),
  )
  let global_p = expect_ok_prover(ks_mk_const(st_out, "P"))
  let global_target = expect_ok_prover(
    prop_mk_imp(st_out, prelude, global_p, global_p),
  )
  let concl = expect_ok_prover(thm_concl(th))
  assert_true(term_logical_eq(concl, local_target))
  assert_false(term_logical_eq(concl, global_target))
}

///|
test "prove_theorem_script_detailed preserves theorem name on success" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let result = prove_theorem_script_detailed(
    st0,
    "theorem t1 : ⊢ P -> P := by exact imp_refl",
    default_prover_options(),
  )
  let ok = expect_proved(result)
  let p = expect_ok_prover(ks_mk_const(ok.state, "P"))
  let prelude = default_prop_prelude()
  let target = expect_ok_prover(prop_mk_imp(ok.state, prelude, p, p))
  let concl = expect_ok_prover(thm_concl(ok.thm))
  assert_eq(ok.theorem_name, "t1")
  assert_true(term_logical_eq(concl, target))
}

///|
test "prove_theorem_script_detailed captures later-step tactic context" {
  let script = "theorem bad : ⊢ T -> T := by intro h; apply truth"
  let result = prove_theorem_script_detailed(
    empty_kernel_state(),
    script,
    default_prover_options(),
  )
  let err = expect_failed(result)
  let st_pre = expect_ok_prover(install_prop_prelude(empty_kernel_state()))
  let prelude = default_prop_prelude()
  let t_term = expect_ok_prover(ks_mk_const(st_pre, prelude.truth_name))

  assert_eq(err.theorem_name, Some("bad"))
  assert_true(
    match err.kind {
      Tactic => true
      _ => false
    },
  )
  assert_true(err.detail.contains("ApplyMismatch"))
  assert_eq(err.step_index, Some(2))
  assert_eq(err.goal_src, Some("⊢ T -> T"))
  match err.goal_span {
    Some(span) => {
      assert_eq(span.start_offset, 14)
      assert_eq(span.end_offset, 22)
    }
    None => panic()
  }
  match err.step_span {
    Some(span) => {
      assert_eq(span.start_offset, 38)
      assert_eq(span.end_offset, 49)
      assert_eq(err.raw_offset, Some(span.start_offset))
    }
    None => panic()
  }
  assert_eq(err.step_src, Some("apply truth"))
  match err.current_goal {
    Some(goal) => {
      assert_eq(goal_hyps(goal).length(), 1)
      assert_true(term_alpha_eq(goal_concl(goal), t_term))
      assert_true(term_alpha_eq(goal_hyps(goal)[0], t_term))
    }
    None => panic()
  }
  assert_eq(err.local_hyps.length(), 1)
  assert_eq(err.local_hyps[0].name, "h")
  assert_true(term_alpha_eq(err.local_hyps[0].term, t_term))
  assert_true(err.error is Tactic(ApplyMismatch(_)))
}

///|
test "prove_theorem_script_detailed leaves parse failures without theorem context" {
  let err = expect_failed(
    prove_theorem_script_detailed(
      empty_kernel_state(),
      "theorem bad : ⊢ T := by ; exact truth",
      default_prover_options(),
    ),
  )
  assert_true(err.theorem_name is None)
  assert_true(
    match err.kind {
      Parse => true
      _ => false
    },
  )
  assert_true(err.detail.contains("offset "))
  assert_eq(err.raw_offset, Some(24))
  assert_true(err.goal_src is None)
  assert_true(err.goal_span is None)
  assert_true(err.step_index is None)
  assert_true(err.step_span is None)
  assert_true(err.step_src is None)
  assert_true(err.current_goal is None)
  assert_eq(err.local_hyps.length(), 0)
  assert_true(err.error is Parse(_))
}

///|
test "prove_theorem_script_detailed records goal location for lowering failures" {
  let err = expect_failed(
    prove_theorem_script_detailed(
      empty_kernel_state(),
      "theorem bad : ⊢ P := by exact truth",
      default_prover_options(),
    ),
  )
  assert_eq(err.theorem_name, Some("bad"))
  assert_true(
    match err.kind {
      Sig => true
      _ => false
    },
  )
  assert_eq(err.goal_src, Some("⊢ P"))
  match err.goal_span {
    Some(span) => {
      assert_eq(span.start_offset, 14)
      assert_eq(span.end_offset, 17)
      assert_eq(err.raw_offset, Some(span.start_offset))
    }
    None => panic()
  }
  assert_true(err.step_index is None)
  assert_true(err.step_span is None)
  assert_true(err.step_src is None)
  assert_true(err.current_goal is None)
  assert_eq(err.local_hyps.length(), 0)
  assert_true(err.error is Sig(_))
}

///|
test "prove_theorem_script_with_diagnostics returns structured qedside failures" {
  let err = expect_diag_failed(
    prove_theorem_script_with_diagnostics(
      empty_kernel_state(),
      "theorem bad : ⊢ T -> T := by intro h",
      default_prover_options(),
    ),
  )
  assert_eq(err.theorem_name, Some("bad"))
  assert_true(
    match err.kind {
      Tactic => true
      _ => false
    },
  )
  assert_true(err.detail.contains("UnsolvedGoals"))
  assert_true(err.step_index is None)
  assert_true(err.step_span is None)
  assert_true(err.step_src is None)
  assert_eq(err.goal_src, Some("⊢ T -> T"))
  match err.current_goal {
    Some(goal) => {
      assert_eq(goal_hyps(goal).length(), 1)
      assert_eq(err.local_hyps.length(), 1)
      assert_eq(err.local_hyps[0].name, "h")
      assert_true(term_alpha_eq(goal_concl(goal), err.local_hyps[0].term))
    }
    None => panic()
  }
}

///|
test "prove_theorem_script accepts explicit structured branch blocks" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))

  let split_script = "theorem t_split : P, Q ⊢ P ∧ Q := by split { assumption } { assumption }"
  let left_script = "theorem t_left : P ⊢ P ∨ Q := by left { assumption }"
  let right_script = "theorem t_right : Q ⊢ P ∨ Q := by right { assumption }"

  assert_true(
    prove_theorem_script(st1, split_script, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, left_script, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, right_script, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script_detailed reports failing split branch path and step" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let err = expect_failed(
    prove_theorem_script_detailed(
      st1,
      "theorem bad : P, Q ⊢ P ∧ Q := by split { assumption } { exact truth }",
      default_prover_options(),
    ),
  )
  assert_eq(err.theorem_name, Some("bad"))
  assert_eq(err.step_index, Some(3))
  assert_eq(err.branch_path, [2])
  assert_true(err.step_src == Some("exact truth"))
  assert_true(err.detail.contains("GoalShapeMismatch"))
  match err.current_goal {
    Some(goal) => assert_eq(goal_hyps(goal).length(), 2)
    None => panic()
  }
}

///|
test "prove_theorem_script_detailed rejects unordered split branch bodies honestly" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let err = expect_failed(
    prove_theorem_script_detailed(
      st1,
      "theorem bad : ⊢ P -> Q -> P ∧ Q := by intro hp; intro hq; split { exact hq } { exact hp }",
      default_prover_options(),
    ),
  )
  assert_eq(err.step_index, Some(4))
  assert_eq(err.branch_path, [1])
  assert_true(err.detail.contains("GoalShapeMismatch"))
}

///|
test "prove_theorem_script_detailed reports invalid disjunction branch body steps" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let err = expect_failed(
    prove_theorem_script_detailed(
      st1,
      "theorem bad : P ⊢ P ∨ Q := by left { intro h }",
      default_prover_options(),
    ),
  )
  assert_eq(err.step_index, Some(2))
  assert_eq(err.branch_path, [1])
  assert_true(err.detail.contains("GoalShapeMismatch"))
  assert_true(err.step_src == Some("intro h"))
}

///|
test "prove_theorem_script accepts block bodies with mixed separators" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let script = "theorem t1 : ⊢ P ∧ Q -> P := by\n  intro h;\n  apply and_elim_l\n  exact h"
  assert_true(
    prove_theorem_script(st1, script, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script supports structured split left right and nested branch blocks" {
  let st = empty_kernel_state()
  let split_script = "theorem t_split : ⊢ T ∧ T := by split { exact truth } { exact truth }"
  let left_script = "theorem t_left : ⊢ T ∨ F := by left { exact truth }"
  let right_script = "theorem t_right : ⊢ F ∨ T := by right { exact truth }"
  assert_true(
    prove_theorem_script(st, split_script, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st, left_script, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st, right_script, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script_detailed records branch path for nested branch failures" {
  let script = "theorem bad : P, Q ⊢ P ∧ (P ∨ Q) := by split { assumption } { right { apply truth } }"
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  let err = expect_failed(
    prove_theorem_script_detailed(st1, script, default_prover_options()),
  )
  assert_eq(err.step_index, Some(4))
  assert_eq(err.branch_path, [2, 1])
  assert_eq(err.step_src, Some("apply truth"))
  match err.step_span {
    Some(span) => assert_eq(err.raw_offset, Some(span.start_offset))
    None => panic()
  }
  assert_true(err.detail.contains("ApplyMismatch"))
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
test "prove_theorem_script supports exact imp_refl by theorem name" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let script = "theorem t1 : ⊢ P -> P := by exact imp_refl"
  let (_st, th) = expect_ok_prover(
    prove_theorem_script(st0, script, default_prover_options()),
  )
  let p = expect_ok_prover(
    ks_mk_const(expect_ok_prover(install_prop_prelude(st0)), "P"),
  )
  let prelude = default_prop_prelude()
  let target = expect_ok_prover(prop_mk_imp(st0, prelude, p, p))
  let concl = expect_ok_prover(thm_concl(th))
  assert_true(term_logical_eq(concl, target))
}

///|
test "prove_theorem_script supports theorem-backed apply names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))

  let script1 = "theorem t2 : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h"
  let script2 = "theorem t3 : ⊢ P -> P ∨ Q := by intro h; apply or_intro_l; exact h"

  assert_true(
    prove_theorem_script(st1, script1, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script2, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script supports exact context-derived and truth names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))

  let script1 = "theorem t4 : P ∧ Q ⊢ P := by exact and_elim_l"
  let script2 = "theorem t5 : ⊢ T := by exact truth"
  let script3 = "theorem t6 : F ⊢ Q := by exact ex_falso"

  assert_true(
    prove_theorem_script(st1, script1, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script2, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script3, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script supports witness-based exact theorem names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))

  let script1 = "theorem t7 : P, Q ⊢ P ∧ Q := by exact and_intro"
  let script2 = "theorem t8 : P -> Q, P ⊢ Q := by exact imp_elim"
  let script3 = "theorem t9 : ⊢ P = P := by exact eq_refl"
  let script4 = "theorem t10 : Q = P ⊢ P = Q := by exact eq_sym"
  let script5 = "theorem t11 : P = Q, P ⊢ Q := by exact eq_mp"

  assert_true(
    prove_theorem_script(st1, script1, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script2, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script3, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script4, default_prover_options()) is Ok(_),
  )
  assert_true(
    prove_theorem_script(st1, script5, default_prover_options()) is Ok(_),
  )
}

///|
test "prove_theorem_script rejects apply on direct-close theorem names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "Q", bool_ty()))
  assert_true(
    prove_theorem_script(
      st0,
      "theorem t : ⊢ T := by apply truth",
      default_prover_options(),
    )
    is Err(Tactic(ApplyMismatch(_))),
  )
  assert_true(
    prove_theorem_script(
      st0,
      "theorem t : F ⊢ Q := by apply ex_falso",
      default_prover_options(),
    )
    is Err(Tactic(ApplyMismatch(_))),
  )
}

///|
test "prove_theorem_script rejects exact on apply-only or unavailable theorem names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  assert_true(
    prove_theorem_script(
      st1,
      "theorem t : ⊢ P -> P ∨ Q := by exact or_intro_l",
      default_prover_options(),
    )
    is Err(Tactic(GoalShapeMismatch(_))),
  )
  assert_true(
    prove_theorem_script(
      st1,
      "theorem t : P ⊢ P := by exact and_elim_l",
      default_prover_options(),
    )
    is Err(Tactic(GoalShapeMismatch(_))),
  )
}

///|
test "prove_theorem_script exact local hypothesis must directly witness the goal" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  assert_true(
    prove_theorem_script(
      st1,
      "theorem t : ⊢ P -> Q -> P := by intro hp; exact hp",
      default_prover_options(),
    )
    is Err(Tactic(GoalShapeMismatch(_))),
  )
}

///|
test "prove_theorem_script rejects apply on incompatible implication-backed names" {
  let st0 = expect_ok_prover(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let st1 = expect_ok_prover(ks_add_const(st0, "Q", bool_ty()))
  assert_true(
    prove_theorem_script(
      st1,
      "theorem t : ⊢ P := by apply and_elim_l",
      default_prover_options(),
    )
    is Err(Tactic(ApplyMismatch(_))),
  )
  assert_true(
    prove_theorem_script(
      st1,
      "theorem t : ⊢ P := by apply missing",
      default_prover_options(),
    )
    is Err(Tactic(UnknownName(_))),
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
