///|
fn parse_err_nonassoc(res : Result[SynTerm, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        NonAssocChain => true
        _ => false
      }
    _ => false
  }
}

///|
fn parse_err_eof(res : Result[SynTerm, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        UnexpectedEof => true
        _ => false
      }
    _ => false
  }
}

///|
fn parse_err_unknown_operator(res : Result[SynTerm, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        UnknownOperator => true
        _ => false
      }
    _ => false
  }
}

///|
fn goal_err_missing_turnstile(res : Result[SynGoal, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        MissingTurnstile => true
        _ => false
      }
    _ => false
  }
}

///|
fn goal_err_empty_concl(res : Result[SynGoal, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        EmptyConclusion => true
        _ => false
      }
    _ => false
  }
}

///|
fn goal_err_empty_hyp(res : Result[SynGoal, ParseError]) -> Bool {
  match res {
    Err(e) =>
      match e.code {
        EmptyHypothesis => true
        _ => false
      }
    _ => false
  }
}

///|
fn bridge_err_nonassoc(res : Result[Term, ParseBridgeError]) -> Bool {
  match res {
    Err(Parse(e)) =>
      match e.code {
        NonAssocChain => true
        _ => false
      }
    _ => false
  }
}

///|
fn bridge_err_unknown_const(res : Result[Term, ParseBridgeError]) -> Bool {
  match res {
    Err(Sig(UnknownConst)) => true
    _ => false
  }
}

///|
fn bridge_err_logic_type_mismatch(res : Result[Term, ParseBridgeError]) -> Bool {
  match res {
    Err(Logic(TypeMismatch)) => true
    _ => false
  }
}

///|
fn bridge_err_sig_definition_not_closed(
  res : Result[(KernelState, Thm), ParseBridgeError],
) -> Bool {
  match res {
    Err(Sig(DefinitionNotClosed)) => true
    _ => false
  }
}

///|
fn[T, E] expect_ok_parser(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn expect_script_step(step : SynScriptStep) -> SynTacticStep {
  step.step
}

///|
fn expect_parse_error(res : Result[SynTerm, ParseError]) -> ParseError {
  match res {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
test "normalize_parser_input canonicalizes escaped operators and whitespace" {
  let norm = expect_ok_parser(
    normalize_parser_input("  theorem  t  :  |-  \\not P \\imp Q \\and R ;  "),
  )
  assert_eq(norm.text, "theorem t : ⊢ ¬ P -> Q ∧ R ;")
  assert_eq(normalized_input_raw_offset_at(norm, 0), 2)
  assert_eq(normalized_input_raw_offset_at(norm, norm.text.length()), 45)
}

///|
test "parse offsets remain aligned to raw input after normalization" {
  let err = expect_parse_error(parse_term_raw("  \\not   (P"))
  assert_true(
    match err.code {
      UnexpectedEof => true
      _ => false
    },
  )
  assert_eq(err.offset, 11)

  let err2 = expect_parse_error(parse_term_raw("P \\xor Q"))
  assert_true(
    match err2.code {
      UnknownOperator => true
      _ => false
    },
  )
  assert_eq(err2.offset, 2)
}

///|
test "parse_term_raw succeeds on base term forms" {
  assert_true(parse_term_raw("P") is Ok(Name("P")))
  assert_true(parse_term_raw("f x") is Ok(App(Name("f"), Name("x"))))
  match parse_term_raw("forall (x : A), P x") {
    Ok(Forall(name, ty, body)) => {
      assert_eq(name, "x")
      assert_true(ty_eq(ty, mk_tyvar("A")))
      assert_true(body is App(Name("P"), Name("x")))
    }
    _ => panic()
  }
  match parse_term_raw("∀ (x : A), P x") {
    Ok(Forall(name, ty, body)) => {
      assert_eq(name, "x")
      assert_true(ty_eq(ty, mk_tyvar("A")))
      assert_true(body is App(Name("P"), Name("x")))
    }
    _ => panic()
  }
  assert_true(
    parse_term_raw("(f x) = y")
    is Ok(Infix("=", App(Name("f"), Name("x")), Name("y"))),
  )
  assert_true(
    parse_term_raw("a = (b = c)")
    is Ok(Infix("=", Name("a"), Infix("=", Name("b"), Name("c")))),
  )
  assert_true(
    parse_term_raw("a ∧ b") is Ok(Infix("∧", Name("a"), Name("b"))),
  )
  assert_true(
    parse_term_raw("a ∨ b") is Ok(Infix("∨", Name("a"), Name("b"))),
  )
  assert_true(
    parse_term_raw("a \\and b") is Ok(Infix("∧", Name("a"), Name("b"))),
  )
  assert_true(
    parse_term_raw("a \\or b") is Ok(Infix("∨", Name("a"), Name("b"))),
  )
  assert_true(
    parse_term_raw("a ∨ b ∧ c")
    is Ok(Infix("∨", Name("a"), Infix("∧", Name("b"), Name("c")))),
  )
  assert_true(
    parse_term_raw("a ∧ b ∧ c")
    is Ok(Infix("∧", Infix("∧", Name("a"), Name("b")), Name("c"))),
  )
  assert_true(parse_term_raw("¬ P") is Ok(Prefix("¬", Name("P"))))
  assert_true(parse_term_raw("\\not P") is Ok(Prefix("¬", Name("P"))))
  assert_true(parse_term_raw("P -> Q") is Ok(Infix("->", Name("P"), Name("Q"))))
  assert_true(
    parse_term_raw("P \\imp Q") is Ok(Infix("->", Name("P"), Name("Q"))),
  )
  assert_true(
    parse_term_raw("¬ P ∨ Q -> R")
    is Ok(
      Infix("->", Infix("∨", Prefix("¬", Name("P")), Name("Q")), Name("R"))
    ),
  )
  assert_true(
    parse_term_raw("Q = P -> P = Q")
    is Ok(
      Infix(
        "->",
        Infix("=", Name("Q"), Name("P")),
        Infix("=", Name("P"), Name("Q"))
      )
    ),
  )
}

///|
test "parse_term_raw reports nonassoc chain and malformed input" {
  assert_true(parse_err_nonassoc(parse_term_raw("a = b = c")))
  assert_true(parse_err_unknown_operator(parse_term_raw("a \\xor b")))
  assert_true(parse_err_unknown_operator(parse_term_raw("\\foo P")))
  assert_true(parse_err_unknown_operator(parse_term_raw("a /\\ b")))
  assert_true(parse_err_unknown_operator(parse_term_raw("a \\/ b")))
  assert_true(parse_term_raw("forall x : A, P x") is Err(_))
  assert_true(parse_term_raw("forall (x : A) P x") is Err(_))
  assert_true(parse_err_eof(parse_term_raw("(P")))
  assert_true(parse_err_eof(parse_term_raw("")))
}

///|
test "parse quantifier raw offsets remain aligned to source input" {
  match parse_term_raw("  forall   (x : A)   P x") {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.detail, "expected `,` after `forall` binder")
      assert_eq(e.offset, 21)
    }
    Ok(_) => panic()
  }
}

///|
test "parse_goal_raw succeeds on standard goal forms" {
  match parse_goal_raw("|- P") {
    Ok(g) => {
      assert_eq(g.hyps.length(), 0)
      assert_true(g.concl is Name("P"))
    }
    Err(_) => panic()
  }

  match parse_goal_raw("⊢ P") {
    Ok(g) => {
      assert_eq(g.hyps.length(), 0)
      assert_true(g.concl is Name("P"))
    }
    Err(_) => panic()
  }

  match parse_goal_raw("P, Q |- P") {
    Ok(g) => {
      assert_eq(g.hyps.length(), 2)
      assert_true(g.hyps[0] is Name("P"))
      assert_true(g.hyps[1] is Name("Q"))
      assert_true(g.concl is Name("P"))
    }
    Err(_) => panic()
  }

  match parse_goal_raw("(f x) = y |- (f x) = y") {
    Ok(g) => {
      assert_eq(g.hyps.length(), 1)
      assert_true(g.hyps[0] is Infix("=", App(Name("f"), Name("x")), Name("y")))
      assert_true(g.concl is Infix("=", App(Name("f"), Name("x")), Name("y")))
    }
    Err(_) => panic()
  }

  match parse_goal_raw("  P , Q   |-   P ") {
    Ok(g) => {
      assert_eq(g.hyps.length(), 2)
      assert_true(g.hyps[0] is Name("P"))
      assert_true(g.hyps[1] is Name("Q"))
      assert_true(g.concl is Name("P"))
    }
    Err(_) => panic()
  }
}

///|
test "parse_goal_raw reports turnstile and hypothesis errors" {
  assert_true(goal_err_missing_turnstile(parse_goal_raw("P, Q P")))
  assert_true(goal_err_empty_concl(parse_goal_raw("|-")))
  assert_true(goal_err_empty_hyp(parse_goal_raw("P, ,Q |- P")))
}

///|
test "parse_term bridge maps parse and kernel errors" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))

  assert_true(parse_term(st2, "P") is Ok(_))
  assert_true(bridge_err_unknown_const(parse_term(st2, "MISSING")))
  assert_true(bridge_err_logic_type_mismatch(parse_term(st2, "P Q")))
  assert_true(bridge_err_nonassoc(parse_term(st2, "P = Q = P")))
}

///|
test "parse_term bridge lowers and/or infix into bool constants" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))
  let st3 = expect_ok_parser(ks_add_const(st2, "R", bool))

  let t_and = expect_ok_parser(parse_term(st3, "P ∧ Q"))
  let t_or = expect_ok_parser(parse_term(st3, "P \\or R"))
  let t_mix = expect_ok_parser(parse_term(st3, "P ∨ Q ∧ R"))
  let t_imp = expect_ok_parser(parse_term(st3, "P -> Q"))
  let t_not = expect_ok_parser(parse_term(st3, "¬ P"))

  assert_true(type_of(t_and) is Some(_))
  assert_true(type_of(t_or) is Some(_))
  assert_true(type_of(t_mix) is Some(_))
  assert_true(type_of(t_imp) is Some(_))
  assert_true(type_of(t_not) is Some(_))
  match type_of(t_mix) {
    Some(ty) => assert_true(ty_eq(ty, bool))
    None => panic()
  }
}

///|
test "bridge expands implication/not without requiring prelude constants in state" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))
  assert_true(parse_term(st2, "P -> Q") is Ok(_))
  assert_true(parse_term(st2, "¬ P") is Ok(_))
}

///|
test "bridge reports structured logic error for non-bool connectors" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let x : A"))
  let env2 = expect_ok_parser(parse_let(env1, "let y : A"))
  assert_true(
    match parse_term_with_env(empty_kernel_state(), env2, "x -> y") {
      Err(Logic(NotBoolTerm)) => true
      _ => false
    },
  )
}

///|
test "parse_goal bridge resolves hypotheses and conclusion" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))
  let p = expect_ok_parser(parse_term(st2, "P"))
  let q = expect_ok_parser(parse_term(st2, "Q"))

  let goal_ok = expect_ok_parser(parse_goal(st2, "P |- P"))
  assert_eq(parsed_goal_hyps(goal_ok).length(), 1)
  assert_true(term_alpha_eq(parsed_goal_hyps(goal_ok)[0], p))
  assert_true(term_alpha_eq(parsed_goal_concl(goal_ok), p))

  let goal_ok_unicode = expect_ok_parser(parse_goal(st2, "P ⊢ P"))
  assert_eq(parsed_goal_hyps(goal_ok_unicode).length(), 1)
  assert_true(term_alpha_eq(parsed_goal_hyps(goal_ok_unicode)[0], p))
  assert_true(term_alpha_eq(parsed_goal_concl(goal_ok_unicode), p))

  let goal_bad = expect_ok_parser(parse_goal(st2, "Q |- P"))
  assert_eq(parsed_goal_hyps(goal_bad).length(), 1)
  assert_true(term_alpha_eq(parsed_goal_hyps(goal_bad)[0], q))
  assert_true(term_alpha_eq(parsed_goal_concl(goal_bad), p))
}

///|
test "let declaration drives Name lowering to local free variables" {
  let bool = bool_ty()
  let st0 = expect_ok_parser(ks_add_const(empty_kernel_state(), "x", bool))
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let x : A"))
  assert_eq(parse_env_local_count(env1), 1)

  let t_local = expect_ok_parser(parse_term_with_env(st0, env1, "x"))
  match dest_var(t_local) {
    Some((name, ty)) => {
      assert_eq(name, "x")
      assert_true(ty_eq(ty, mk_tyvar("A")))
    }
    None => panic()
  }

  let t_global = expect_ok_parser(parse_term(st0, "x"))
  match dest_const(t_global) {
    Some((name, ty)) => {
      assert_eq(name, "x")
      assert_true(ty_eq(ty, bool))
    }
    None => panic()
  }
}

///|
test "let declaration parses arrow type for free variable" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let f : A -> bool"))
  let (_, ty) = match parse_env_local_at(env1, 0) {
    Some(v) => v
    None => panic()
  }
  assert_true(ty_eq(ty, fun_ty(mk_tyvar("A"), bool_ty())))
}

///|
test "let and def declarations accept normalized compatible input" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "  let   f  :  A \\imp bool "))
  let (_, ty) = match parse_env_local_at(env1, 0) {
    Some(v) => v
    None => panic()
  }
  assert_true(ty_eq(ty, fun_ty(mk_tyvar("A"), bool_ty())))

  let st0 = empty_kernel_state()
  let (st1, _) = expect_ok_parser(
    parse_def_function(st0, empty_parse_env(), "def id(x : A) : A {  x  }"),
  )
  let id_term = expect_ok_parser(parse_term(st1, "id"))
  assert_true(type_of(id_term) is Some(_))
}

///|
test "parse_goal_with_env can consume local propositions" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let p : bool"))
  let st = empty_kernel_state()
  let goal = expect_ok_parser(parse_goal_with_env(st, env1, "p ⊢ p"))
  let term = expect_ok_parser(parse_term_with_env(st, env1, "p"))
  assert_eq(parsed_goal_hyps(goal).length(), 1)
  assert_true(term_alpha_eq(parsed_goal_hyps(goal)[0], term))
  assert_true(term_alpha_eq(parsed_goal_concl(goal), term))
}

///|
test "parse_resolved_term_with_env freezes const identity across shadowing" {
  let bool = bool_ty()
  let st0 = expect_ok_parser(ks_add_const(empty_kernel_state(), "P", bool))
  let rt0 = expect_ok_parser(
    parse_resolved_term_with_env(st0, empty_parse_env(), "P"),
  )
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_parser(ks_add_const(st1, "P", fun_ty(bool, bool)))
  let rt1 = expect_ok_parser(
    parse_resolved_term_with_env(st2, empty_parse_env(), "P"),
  )

  match (rt0, rt1) {
    (RConst(c0), RConst(c1)) => {
      assert_false(rconst_id(c0) == rconst_id(c1))
      let lowered0 = expect_ok_parser(elab_lower_to_term(rterm_const(c0)))
      match type_of(lowered0) {
        Some(ty) => assert_true(ty_eq(ty, bool))
        None => panic()
      }
    }
    _ => panic()
  }
}

///|
test "def function declaration builds lambda-backed constant definition" {
  let st0 = empty_kernel_state()
  let env = empty_parse_env()
  let (st1, _) = expect_ok_parser(
    parse_def_function(st0, env, "def id(x : A) : A { x }"),
  )
  let id_term = expect_ok_parser(parse_term(st1, "id"))
  match type_of(id_term) {
    Some(ty) => assert_true(ty_eq(ty, fun_ty(mk_tyvar("A"), mk_tyvar("A"))))
    None => panic()
  }
}

///|
test "resolved terms remain typable after scope pop" {
  let bool = bool_ty()
  let st0 = expect_ok_parser(ks_add_const(empty_kernel_state(), "P", bool))
  let st1 = ks_push_scope(st0)
  let rt = expect_ok_parser(
    parse_resolved_term_with_env(st1, empty_parse_env(), "P"),
  )
  let st2 = expect_ok_parser(ks_pop_scope(st1))
  assert_true(elab_core_type_of(st2, empty_elab_ctx(), rt) is Some(_))
}

///|
test "lowered parsed terms preserve frozen const identity across same-typed shadowing" {
  let bool = bool_ty()
  let st0 = expect_ok_parser(ks_add_const(empty_kernel_state(), "P", bool))
  let old_term = expect_ok_parser(parse_term(st0, "P"))
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_parser(ks_add_const(st1, "P", bool))
  assert_true(refl_checked(st2, old_term) is Err(InvalidInstantiation))
}

///|
test "def function body cannot capture outer free variables" {
  let st0 = empty_kernel_state()
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let y : A"))
  assert_true(
    bridge_err_sig_definition_not_closed(
      parse_def_function(st0, env1, "def bad(x : A) : A { y }"),
    ),
  )
}

///|
test "lowering keeps let variable as debruijn free var" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let y : A"))
  let st = empty_kernel_state()
  let term = expect_ok_parser(parse_term_with_env(st, env1, "y"))
  match to_db_term(term) {
    Some(db) => assert_true(db_term_to_string(db).contains("FVar(y : A)"))
    None => panic()
  }
}

///|
test "def lowering binds parameter at debruijn index 0" {
  let st0 = empty_kernel_state()
  let env = empty_parse_env()
  let (_, th) = expect_ok_parser(
    parse_def_function(st0, env, "def id(x : A) : A { x }"),
  )
  let concl = expect_ok_parser(thm_concl(th))
  let (_, rhs) = expect_ok_parser(dest_eq(concl))
  match to_db_term(rhs) {
    Some(db) => assert_true(db_term_to_string(db).contains("BVar(0 : A)"))
    None => panic()
  }
}

///|
test "parse theorem script raw supports theorem header binders" {
  let src = "theorem t1 (P : bool) (Q : A -> bool) : ⊢ P -> P := by intro h; exact h"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.name, "t1")
      assert_eq(s.binders.length(), 2)
      assert_eq(s.binders[0].name, "P")
      assert_true(ty_eq(s.binders[0].ty, bool_ty()))
      assert_eq(s.binders[0].src, "(P : bool)")
      assert_eq(s.binders[1].name, "Q")
      assert_true(ty_eq(s.binders[1].ty, fun_ty(mk_tyvar("A"), bool_ty())))
      assert_eq(s.binders[1].src, "(Q : A -> bool)")
      assert_true(
        s.binders[0].span.start_offset < s.binders[1].span.start_offset,
      )
      assert_true(s.binders[1].span.end_offset <= s.goal_span.start_offset)
      assert_eq(s.goal_src, "⊢ P -> P")
      assert_eq(s.body.steps.length(), 2)
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[1].step_index, 2)
      assert_eq(s.body.steps[1].branch_path, [])
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw supports linear by-steps" {
  let src = "theorem t1 : ⊢ P -> P := by intro h; exact h"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.name, "t1")
      assert_eq(s.goal_span.start_offset, 13)
      assert_eq(s.goal_span.end_offset, 21)
      assert_eq(s.body.steps.length(), 2)
      assert_true(expect_script_step(s.body.steps[0]) is Intro("h"))
      assert_eq(s.body.steps[0].src, "intro h")
      assert_eq(s.body.steps[0].span.start_offset, 28)
      assert_eq(s.body.steps[0].span.end_offset, 35)
      assert_true(expect_script_step(s.body.steps[1]) is Exact("h"))
      assert_eq(s.body.steps[1].src, "exact h")
      assert_eq(s.body.steps[1].span.start_offset, 37)
      assert_eq(s.body.steps[1].span.end_offset, 44)
      assert_eq(s.goal.hyps.length(), 0)
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw supports hole steps" {
  match parse_theorem_script_raw("theorem t1 : ⊢ P := by hole") {
    Ok(s) => {
      assert_eq(s.body.steps.length(), 1)
      assert_true(expect_script_step(s.body.steps[0]) is Hole(None))
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[0].src, "hole")
      assert_eq(s.body.steps[0].span.start_offset, 23)
      assert_eq(s.body.steps[0].span.end_offset, 27)
    }
    Err(_) => panic()
  }

  match parse_theorem_script_raw("theorem t1 : ⊢ P := by hole h1") {
    Ok(s) => {
      assert_eq(s.body.steps.length(), 1)
      assert_true(expect_script_step(s.body.steps[0]) is Hole(Some("h1")))
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[0].src, "hole h1")
      assert_eq(s.body.steps[0].span.start_offset, 23)
      assert_eq(s.body.steps[0].span.end_offset, 30)
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw normalizes turnstile escapes and keeps raw offsets" {
  let src = "theorem t1 :  |-  P \\imp P := by intro h; exact h"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.name, "t1")
      assert_eq(s.goal_src, "⊢ P -> P")
      assert_eq(s.body.steps.length(), 2)
    }
    Err(_) => panic()
  }

  match
    parse_theorem_script_raw("theorem t1 :  |-  P \\imp P := by ; exact h") {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.offset, 33)
    }
    Ok(_) => panic()
  }
}

///|
test "parse theorem script raw rejects malformed theorem binders" {
  match
    parse_theorem_script_raw("theorem t (P Q : bool) : ⊢ P := by exact truth") {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.offset, 13)
    }
    Ok(_) => panic()
  }
}

///|
test "parse theorem script raw supports block bodies and mixed separators" {
  let src = "theorem t1 : ⊢ P -> P := by\n  intro h;\n  exact h"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.name, "t1")
      assert_eq(s.body.steps.length(), 2)
      assert_true(expect_script_step(s.body.steps[0]) is Intro("h"))
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[0].src, "intro h")
      assert_true(expect_script_step(s.body.steps[1]) is Exact("h"))
      assert_eq(s.body.steps[1].step_index, 2)
      assert_eq(s.body.steps[1].branch_path, [])
      assert_eq(s.body.steps[1].src, "exact h")
      assert_true(
        s.body.steps[0].span.start_offset < s.body.steps[1].span.start_offset,
      )
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw supports structured branch blocks" {
  let src = "theorem t1 : P, Q ⊢ P ∧ Q := by split { assumption } { assumption }"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.body.steps.length(), 1)
      assert_true(expect_script_step(s.body.steps[0]) is Split)
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[0].src, "split")
      assert_eq(s.body.steps[0].branches.length(), 2)
      assert_eq(s.body.steps[0].branches[0].branch_path, [1])
      assert_eq(s.body.steps[0].branches[0].body.steps.length(), 1)
      assert_true(
        expect_script_step(s.body.steps[0].branches[0].body.steps[0])
        is Assumption,
      )
      assert_eq(s.body.steps[0].branches[0].body.steps[0].step_index, 2)
      assert_eq(s.body.steps[0].branches[0].body.steps[0].branch_path, [1])
      assert_eq(s.body.steps[0].branches[0].src, "{ assumption }")
      assert_eq(s.body.steps[0].branches[1].branch_path, [2])
      assert_eq(s.body.steps[0].branches[1].body.steps.length(), 1)
      assert_true(
        expect_script_step(s.body.steps[0].branches[1].body.steps[0])
        is Assumption,
      )
      assert_eq(s.body.steps[0].branches[1].body.steps[0].step_index, 3)
      assert_eq(s.body.steps[0].branches[1].body.steps[0].branch_path, [2])
      assert_true(
        s.body.steps[0].span.end_offset <=
        s.body.steps[0].branches[0].span.start_offset,
      )
      assert_true(
        s.body.steps[0].branches[0].span.end_offset <=
        s.body.steps[0].branches[1].span.start_offset,
      )
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw supports quantifier goals mixed with binders and branch blocks" {
  let src = "theorem t1 (P : A -> bool) : ⊢ forall (x : A), P x ∧ P x := by split { hole } { hole h1 }"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.binders.length(), 1)
      assert_eq(s.body.steps.length(), 1)
      assert_true(expect_script_step(s.body.steps[0]) is Split)
      assert_eq(s.body.steps[0].step_index, 1)
      assert_eq(s.body.steps[0].branch_path, [])
      assert_eq(s.body.steps[0].branches.length(), 2)
      match s.goal.concl {
        Forall(name, ty, body) => {
          assert_eq(name, "x")
          assert_true(ty_eq(ty, mk_tyvar("A")))
          assert_true(
            body
            is Infix(
              "∧",
              App(Name("P"), Name("x")),
              App(Name("P"), Name("x"))
            ),
          )
        }
        _ => panic()
      }
      assert_true(
        expect_script_step(s.body.steps[0].branches[0].body.steps[0])
        is Hole(None),
      )
      assert_eq(s.body.steps[0].branches[0].branch_path, [1])
      assert_eq(s.body.steps[0].branches[0].body.steps[0].step_index, 2)
      assert_eq(s.body.steps[0].branches[0].body.steps[0].branch_path, [1])
      assert_true(
        expect_script_step(s.body.steps[0].branches[1].body.steps[0])
        is Hole(Some("h1")),
      )
      assert_eq(s.body.steps[0].branches[1].branch_path, [2])
      assert_eq(s.body.steps[0].branches[1].body.steps[0].step_index, 3)
      assert_eq(s.body.steps[0].branches[1].body.steps[0].branch_path, [2])
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw rejects malformed quantifier goals" {
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ forall x : A, P x := by hole")
    is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ forall (x : A) P x := by hole")
    is Err(_),
  )
}

///|
test "parse goal bridge rejects quantifier goals on the shipped path" {
  let env0 = expect_ok_parser(parse_let(empty_parse_env(), "let x : bool"))
  match
    parse_goal_with_env(
      empty_kernel_state(),
      env0,
      "x ⊢ forall (x : A), x = x",
    ) {
    Err(Parse(e)) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(
        e.detail,
        "quantifier frontend is not yet resolved on the shipped path",
      )
    }
    Ok(_) => panic()
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw supports nested structured branch blocks" {
  let src = "theorem t1 : P, Q ⊢ P ∧ (P ∨ Q) := by split { assumption } { left { assumption } }"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      let split_step = s.body.steps[0]
      assert_eq(split_step.branches.length(), 2)
      let left_step = split_step.branches[1].body.steps[0]
      assert_true(expect_script_step(left_step) is Left)
      assert_eq(left_step.step_index, 3)
      assert_eq(left_step.branch_path, [2])
      assert_eq(left_step.src, "left")
      assert_eq(left_step.branches.length(), 1)
      assert_eq(left_step.branches[0].branch_path, [2, 1])
      assert_eq(left_step.branches[0].src, "{ assumption }")
      assert_true(
        expect_script_step(left_step.branches[0].body.steps[0]) is Assumption,
      )
      assert_eq(left_step.branches[0].body.steps[0].step_index, 4)
      assert_eq(left_step.branches[0].body.steps[0].branch_path, [2, 1])
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw keeps raw spans for structured branch blocks" {
  let src = "theorem t1 :  |-  P \\imp P := by left { exact h }"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      let step = s.body.steps[0]
      assert_eq(step.src, "left")
      assert_eq(step.step_index, 1)
      assert_eq(step.branch_path, [])
      assert_eq(step.span.start_offset, 33)
      assert_eq(step.span.end_offset, 37)
      assert_eq(step.branches.length(), 1)
      assert_eq(step.branches[0].branch_path, [1])
      assert_eq(step.branches[0].src, "{ exact h }")
      assert_eq(step.branches[0].span.start_offset, 38)
      assert_eq(step.branches[0].span.end_offset, 49)
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw captures explicit branch blocks" {
  let src = "theorem t1 : P, Q ⊢ P ∧ Q := by split { assumption } { assumption }"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.body.steps.length(), 1)
      let step = s.body.steps[0]
      assert_true(expect_script_step(step) is Split)
      assert_eq(step.step_index, 1)
      assert_eq(step.branch_path, [])
      assert_eq(step.branches.length(), 2)
      assert_eq(step.branches[0].body.steps.length(), 1)
      assert_eq(step.branches[1].body.steps.length(), 1)
      assert_eq(step.branches[0].branch_path, [1])
      assert_eq(step.branches[1].branch_path, [2])
      assert_true(
        expect_script_step(step.branches[0].body.steps[0]) is Assumption,
      )
      assert_true(
        expect_script_step(step.branches[1].body.steps[0]) is Assumption,
      )
      assert_eq(step.branches[0].body.steps[0].step_index, 2)
      assert_eq(step.branches[0].body.steps[0].branch_path, [1])
      assert_eq(step.branches[1].body.steps[0].step_index, 3)
      assert_eq(step.branches[1].body.steps[0].branch_path, [2])
      assert_eq(step.branches[0].src, "{ assumption }")
      assert_eq(step.branches[1].src, "{ assumption }")
      assert_true(
        step.branches[0].span.start_offset < step.branches[1].span.start_offset,
      )
    }
    Err(_) => panic()
  }
}

///|
test "parse theorem script raw rejects incorrect branch block arity" {
  match
    parse_theorem_script_raw(
      "theorem t : ⊢ P := by exact truth { exact truth }",
    ) {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(
        e.detail,
        "tactic step does not accept structured branch blocks",
      )
    }
    Ok(_) => panic()
  }

  match
    parse_theorem_script_raw(
      "theorem t : P, Q ⊢ P ∧ Q := by split { assumption }",
    ) {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.detail, "incorrect number of branch blocks for tactic step")
    }
    Ok(_) => panic()
  }
}

///|
test "parse theorem script raw keeps raw offsets for block body errors" {
  let src = "theorem t1 : ⊢ P -> P := by\n\nexact h"
  match parse_theorem_script_raw(src) {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.offset, 28)
    }
    Ok(_) => panic()
  }
}

///|
test "parse theorem script raw rejects malformed structured branch blocks" {
  match parse_theorem_script_raw("theorem t : ⊢ P := by { exact h }") {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.offset, 22)
      assert_eq(
        e.detail,
        "branch block must follow `split`, `left`, or `right`",
      )
    }
    Ok(_) => panic()
  }

  match parse_theorem_script_raw("theorem t : ⊢ P := by left { exact h") {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedEof => true
          _ => false
        },
      )
      assert_eq(e.detail, "missing `}` to close branch block")
      assert_eq(e.offset, 27)
    }
    Ok(_) => panic()
  }

  match
    parse_theorem_script_raw(
      "theorem t : ⊢ P ∧ Q := by split { assumption } { left { assumption } assumption }",
    ) {
    Err(e) => {
      assert_true(
        match e.code {
          UnexpectedToken => true
          _ => false
        },
      )
      assert_eq(e.detail, "expected tactic separator")
    }
    Ok(_) => panic()
  }
}

///|
test "parse theorem script raw rejects malformed bodies" {
  assert_true(parse_theorem_script_raw("theorem t : ⊢ P := by") is Err(_))
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ P by intro h") is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ P := by ; exact h") is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ P := by intro h\n; exact h")
    is Err(_),
  )
  assert_true(
    parse_theorem_script_raw(
      "theorem t : P, Q ⊢ P ∧ Q := by split { assumption }",
    )
    is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : P ⊢ P := by intro h { exact h }")
    is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ P := by left }") is Err(_),
  )
  assert_true(
    parse_theorem_script_raw("theorem t : ⊢ P := by hole h1 h2") is Err(_),
  )
}
