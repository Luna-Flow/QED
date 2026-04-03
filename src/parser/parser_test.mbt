///|
using @kernel {
  type Term,
  type KernelState,
  type Thm,
  bool_ty,
  empty_kernel_state,
  ks_add_const,
  mk_tyvar,
  ty_eq,
  fun_ty,
  dest_var,
  dest_const,
  refl_checked,
  type_of,
  to_db_term,
  db_term_to_string,
  thm_concl,
  dest_eq,
  ks_pop_scope,
  ks_push_scope,
}

///|
using @tactics {solve_by_hyp}

///|
using @elab {
  empty_elab_ctx,
  elab_core_type_of,
  elab_lower_to_term,
  rconst_id,
  rterm_const,
}

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
test "parse_term_raw succeeds on base term forms" {
  assert_true(parse_term_raw("P") is Ok(Name("P")))
  assert_true(parse_term_raw("f x") is Ok(App(Name("f"), Name("x"))))
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
}

///|
test "parse_term_raw reports nonassoc chain and malformed input" {
  assert_true(parse_err_nonassoc(parse_term_raw("a = b = c")))
  assert_true(parse_err_unknown_operator(parse_term_raw("a \\xor b")))
  assert_true(parse_err_unknown_operator(parse_term_raw("\\foo P")))
  assert_true(parse_err_eof(parse_term_raw("(P")))
  assert_true(parse_err_eof(parse_term_raw("")))
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
  let bool_binop = fun_ty(bool, fun_ty(bool, bool))
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))
  let st3 = expect_ok_parser(ks_add_const(st2, "R", bool))
  let st4 = expect_ok_parser(ks_add_const(st3, "and", bool_binop))
  let st5 = expect_ok_parser(ks_add_const(st4, "or", bool_binop))
  let st6 = expect_ok_parser(ks_add_const(st5, "imp", bool_binop))
  let st7 = expect_ok_parser(ks_add_const(st6, "not", fun_ty(bool, bool)))

  let t_and = expect_ok_parser(parse_term(st7, "P ∧ Q"))
  let t_or = expect_ok_parser(parse_term(st7, "P \\or R"))
  let t_mix = expect_ok_parser(parse_term(st7, "P ∨ Q ∧ R"))
  let t_imp = expect_ok_parser(parse_term(st7, "P -> Q"))
  let t_not = expect_ok_parser(parse_term(st7, "¬ P"))

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
test "bridge for implication/not reports unknown constants when prelude absent" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))
  assert_true(bridge_err_unknown_const(parse_term(st2, "P -> Q")))
  assert_true(bridge_err_unknown_const(parse_term(st2, "¬ P")))
}

///|
test "parse_goal bridge works with tactics solve_by_hyp" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_parser(ks_add_const(st0, "P", bool))
  let st2 = expect_ok_parser(ks_add_const(st1, "Q", bool))

  let goal_ok = expect_ok_parser(parse_goal(st2, "P |- P"))
  assert_true(solve_by_hyp(st2, goal_ok) is Ok(_))

  let goal_ok_unicode = expect_ok_parser(parse_goal(st2, "P ⊢ P"))
  assert_true(solve_by_hyp(st2, goal_ok_unicode) is Ok(_))

  let goal_bad = expect_ok_parser(parse_goal(st2, "Q |- P"))
  assert_true(solve_by_hyp(st2, goal_bad) is Err(AlphaMismatch))
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
test "parse_goal_with_env can consume local propositions" {
  let env0 = empty_parse_env()
  let env1 = expect_ok_parser(parse_let(env0, "let p : bool"))
  let st = empty_kernel_state()
  let goal = expect_ok_parser(parse_goal_with_env(st, env1, "p ⊢ p"))
  assert_true(solve_by_hyp(st, goal) is Ok(_))
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
test "parse theorem script raw supports linear by-steps" {
  let src = "theorem t1 : ⊢ P -> P := by intro h; exact h"
  match parse_theorem_script_raw(src) {
    Ok(s) => {
      assert_eq(s.name, "t1")
      assert_eq(s.steps.length(), 2)
      assert_true(s.steps[0] is Intro("h"))
      assert_true(s.steps[1] is Exact("h"))
      assert_eq(s.goal.hyps.length(), 0)
    }
    Err(_) => panic()
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
}
