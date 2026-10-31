// Conformance tests for the extension gates of the Lean model.
//
// The gates are the structures `DefinitionGate` (Definitions.lean),
// `SpecificationGate` (Specification.lean) and `TypeDefGate`
// (TypeDefGate.lean); the theorems they publish are the constructors
// `definition`, `specification` and `typedef` of `HistoryDerivation`, with the
// three laws of `TypeDefLaw`. Each test is named after the Lean field or
// constructor it follows: a field that is data is checked against what the
// kernel builds, and a field that is a premise is enforced with a negative case.

///|
fn[T, E] le_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn le_eq(lhs : Term, rhs : Term) -> Term {
  le_ok(mk_eq(lhs, rhs))
}

///|
fn le_concl_is(th : Thm, expected : Term) -> Bool {
  term_alpha_eq(le_ok(thm_concl(th)), expected)
}

///|
fn le_hyps_are(th : Thm, expected : Array[Term]) -> Bool {
  let hyps = le_ok(thm_hyps(th))
  hyps.length() == expected.length() &&
  expected.all(e => hyps.any(h => term_alpha_eq(h, e)))
}

///|
/// `@ (λw. w = w)`, a closed term of any type.
fn le_closed_term(ty : HolType) -> Term {
  let w = mk_var("w", ty)
  mk_comb(
    mk_const("@", fun_ty(fun_ty(ty, bool_ty()), ty)),
    mk_abs(w, le_eq(w, w)),
  )
}

///|
/// `λx. x = x` at `ty`, true of every element.
fn le_refl_pred(ty : HolType) -> Term {
  let x = mk_var("x", ty)
  mk_abs(x, le_eq(x, x))
}

///|
/// `⊢ w = w` for the closed term w, a witness of `le_refl_pred`.
fn le_refl_witness(st : KernelState, ty : HolType) -> Thm {
  le_ok(refl_checked(st, le_closed_term(ty)))
}

// --- DefinitionGate ---------------------------------------------------------

///|
test "DefinitionGate.id: each definition allocates a fresh identity" {
  let st0 = empty_kernel_state()
  let rhs = le_closed_term(bool_ty())
  let (st1, _) = le_ok(ks_define_const(st0, "d1", bool_ty(), rhs))
  let (st2, _) = le_ok(ks_define_const(st1, "d2", bool_ty(), rhs))
  let id1 = ks_lookup_const_id(st2, "d1").unwrap()
  let id2 = ks_lookup_const_id(st2, "d2").unwrap()
  assert_true(id1 != id2)
  assert_true(id2 > id1)
}

///|
test "DefinitionGate.rhs: a closed term of the declared type" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  // Free variables are not allowed: rhs : Term S [] _.
  assert_true(
    ks_define_const(st, "d", a, mk_var("x", a)) is Err(DefinitionNotClosed),
  )
  // The type of rhs is the type of the constant: rhs : Term S [] (S id).
  assert_true(
    ks_define_const(st, "d", bool_ty(), le_closed_term(a)) is Err(TypeMismatch),
  )
  // rhs is a term of the current signature.
  assert_true(
    ks_define_const(st, "d", bool_ty(), mk_const("unknown", bool_ty()))
    is Err(_),
  )
}

///|
test "DefinitionGate.fresh: the constant does not occur in its right-hand side" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let f = fun_ty(bool, bool)
  let x = mk_var("x", bool)
  let cyclic = mk_abs(x, mk_comb(mk_const("d", f), x))
  assert_true(ks_define_const(st0, "d", f, cyclic) is Err(DefinitionIsCyclic))
  // Also when the name already denotes an older constant: the published
  // theorem would mention the new constant.
  let st1 = le_ok(ks_add_const(st0, "d", f))
  assert_true(ks_define_const(st1, "d", f, cyclic) is Err(_))
}

///|
test "DefinitionGate.typeVarsClosed: every annotation type variable is in the type" {
  let st = empty_kernel_state()
  // `(λx:B. x = x) = (λx:B. x = x)` has type bool but mentions B in a binder.
  let lam = le_refl_pred(mk_tyvar("B"))
  assert_true(
    ks_define_const(st, "d", bool_ty(), le_eq(lam, lam))
    is Err(GhostTypeVariable),
  )
  // A type variable of the declared type is allowed.
  let a = mk_tyvar("A")
  assert_true(
    ks_define_const(st, "d", fun_ty(a, bool_ty()), le_refl_pred(a)) is Ok(_),
  )
}

///|
test "HistoryDerivation.definition: publishes ⊢ c = rhs" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let ty = fun_ty(a, bool_ty())
  let rhs = le_refl_pred(a)
  let (st1, th) = le_ok(ks_define_const_thm(st0, "d", ty, rhs))
  let c = le_ok(ks_mk_const(st1, "d"))
  assert_true(le_concl_is(th, le_eq(c, rhs)))
  assert_true(le_hyps_are(th, []))
  assert_true(thm_is_admissible(st1, th))
}

///|
test "HistoryDerivation.definition: the constant is fresh in the history" {
  let st0 = empty_kernel_state()
  let rhs = le_closed_term(bool_ty())
  let (st1, _) = le_ok(ks_define_const(st0, "d", bool_ty(), rhs))
  assert_true(
    ks_define_const(st1, "d", bool_ty(), rhs) is Err(DefinitionAlreadyExists),
  )
}

// --- SpecificationGate ------------------------------------------------------

///|
test "SpecificationGate.id: a specification allocates a fresh identity" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let (st1, _) = le_ok(
    ks_specify_const(
      st0,
      "s1",
      bool,
      le_refl_pred(bool),
      le_refl_witness(st0, bool),
    ),
  )
  let (st2, _) = le_ok(
    ks_specify_const(
      st1,
      "s2",
      bool,
      le_refl_pred(bool),
      le_refl_witness(st1, bool),
    ),
  )
  assert_true(
    ks_lookup_const_id(st2, "s1").unwrap() !=
    ks_lookup_const_id(st2, "s2").unwrap(),
  )
}

///|
test "SpecificationGate.ty: the declared type is the predicate's domain" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let witness = le_refl_witness(st, bool_ty())
  assert_true(
    ks_specify_const(st, "s", a, le_refl_pred(bool_ty()), witness)
    is Err(InvalidSpecificationPredicate),
  )
}

///|
test "SpecificationGate.predicate: a closed abstraction into bool" {
  let st = empty_kernel_state()
  let bool = bool_ty()
  let witness = le_refl_witness(st, bool)
  let x = mk_var("x", bool)
  let y = mk_var("y", bool)
  // Not an abstraction.
  assert_true(
    ks_specify_const(st, "s", bool, le_eq(x, x), witness)
    is Err(InvalidSpecificationPredicate),
  )
  // Open: y is free.
  assert_true(
    ks_specify_const(st, "s", bool, mk_abs(x, le_eq(x, y)), witness)
    is Err(InvalidSpecificationPredicate),
  )
  // Body not boolean.
  assert_true(
    ks_specify_const(st, "s", bool, mk_abs(x, mk_abs(y, y)), witness)
    is Err(InvalidSpecificationPredicate),
  )
}

///|
test "SpecificationGate.witness: a closed term with a hypothesis-free proof of P w" {
  let st = empty_kernel_state()
  let bool = bool_ty()
  let pred = le_refl_pred(bool)
  // A hypothesis is not allowed.
  let p = mk_var("p", bool)
  let with_hyp = le_ok(add_assum_checked(st, p, le_refl_witness(st, bool)))
  assert_true(
    ks_specify_const(st, "s", bool, pred, with_hyp)
    is Err(InvalidSpecificationWitness),
  )
  // The witness must be closed: ⊢ p = p only proves P at a free p.
  let open = le_ok(refl_checked(st, p))
  assert_true(
    ks_specify_const(st, "s", bool, pred, open)
    is Err(InvalidSpecificationWitness),
  )
  // The theorem must prove P w, not something else.
  let other = le_ok(refl_checked(st, le_refl_pred(bool)))
  assert_true(
    ks_specify_const(st, "s", bool, pred, other)
    is Err(InvalidSpecificationWitness),
  )
}

///|
test "SpecificationGate.fresh: the constant does not occur in the predicate" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let st1 = le_ok(ks_add_const(st0, "s", bool))
  let x = mk_var("x", bool)
  let s_old = le_ok(ks_mk_const(st1, "s"))
  let pred = mk_abs(x, le_eq(x, s_old))
  let witness = le_ok(refl_checked(st1, s_old))
  assert_true(ks_specify_const(st1, "s", bool, pred, witness) is Err(_))
}

///|
test "SpecificationGate.typeVarsClosed: every annotation type variable is in the type" {
  let st = empty_kernel_state()
  let bool = bool_ty()
  let x = mk_var("x", bool)
  let ghost = le_refl_pred(mk_tyvar("B"))
  let pred = mk_abs(x, le_eq(ghost, ghost))
  let witness = le_ok(refl_checked(st, ghost))
  assert_true(
    ks_specify_const(st, "s", bool, pred, witness)
    is Err(SpecificationTypeVarLeak),
  )
}

///|
test "HistoryDerivation.specification: publishes ⊢ P[c/x]" {
  // Lean publishes `predicate.substitute (Sub.single c)`, the beta-reduct.
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let pred = le_refl_pred(fun_ty(a, a))
  let witness = le_refl_witness(st0, fun_ty(a, a))
  let (st1, th) = le_ok(ks_specify_const(st0, "s", fun_ty(a, a), pred, witness))
  let c = le_ok(ks_mk_const(st1, "s"))
  assert_true(le_concl_is(th, le_eq(c, c)))
  assert_true(le_hyps_are(th, []))
  assert_true(thm_is_admissible(st1, th))
}

// --- TypeDefGate ------------------------------------------------------------

///|
fn le_typedef(
  st : KernelState,
  tycon : String,
  params : Array[String],
  rep : String,
  rep_ty : HolType,
) -> Result[KernelState, SigError] {
  ks_register_type_definition(
    st,
    tycon,
    params,
    rep,
    le_refl_pred(rep_ty),
    le_refl_witness(st, rep_ty),
  )
}

///|
test "TypeDefGate.k: the new type constructor becomes available" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let new_ty = mk_tyapp("box", [a])
  assert_false(ks_type_is_admissible(st0, new_ty))
  let st1 = le_ok(le_typedef(st0, "box", ["A"], "rep_box", a))
  assert_true(ks_type_is_admissible(st1, new_ty))
  assert_true(le_typedef(st0, "", ["A"], "rep_box", a) is Err(_))
}

///|
test "TypeDefGate.n: the arity is the number of distinct type parameters" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let st1 = le_ok(le_typedef(st0, "pair2", ["A", "B"], "rep_pair2", a))
  assert_true(
    ks_type_is_admissible(st1, mk_tyapp("pair2", [bool_ty(), bool_ty()])),
  )
  assert_false(ks_type_is_admissible(st1, mk_tyapp("pair2", [bool_ty()])))
  assert_true(
    le_typedef(st0, "t", ["A", "A"], "rep_t", a) is Err(InvalidTypeParams),
  )
  assert_true(le_typedef(st0, "t", [""], "rep_t", a) is Err(InvalidTypeParams))
}

///|
test "TypeDefGate.repTy: the representation type is the predicate's domain" {
  let st0 = empty_kernel_state()
  let rep_ty = fun_ty(bool_ty(), bool_ty())
  let st1 = le_ok(le_typedef(st0, "fb", [], "rep_fb", rep_ty))
  let schema = ks_const_schema(st1, "rep_fb").unwrap()
  assert_true(ty_eq(schema, fun_ty(mk_tyapp("fb", []), rep_ty)))
}

///|
test "TypeDefGate.pred: a closed abstraction into bool" {
  let st = empty_kernel_state()
  let bool = bool_ty()
  let witness = le_refl_witness(st, bool)
  let x = mk_var("x", bool)
  let y = mk_var("y", bool)
  for bad in [le_eq(x, x), mk_abs(x, le_eq(x, y)), mk_abs(x, mk_abs(y, y))] {
    assert_true(
      ks_register_type_definition(st, "t", [], "rep_t", bad, witness) is Err(_),
    )
  }
}

///|
test "TypeDefGate.rep: the representation constant is added" {
  let st0 = empty_kernel_state()
  assert_true(ks_lookup_const(st0, "rep_u") is None)
  let st1 = le_ok(le_typedef(st0, "u", [], "rep_u", bool_ty()))
  assert_true(ks_lookup_const(st1, "rep_u") is Some(_))
  assert_true(ks_has_type_rep_head(st1, "rep_u"))
}

///|
test "TypeDefGate.abs: the abstraction constant is added" {
  let st1 = le_ok(le_typedef(empty_kernel_state(), "u", [], "rep_u", bool_ty()))
  assert_true(ks_lookup_const(st1, "Abs_u") is Some(_))
  assert_true(ks_has_type_abs_head(st1, "Abs_u"))
}

///|
test "TypeDefGate.rep_ty: rep : k(α) -> repTy" {
  let a = mk_tyvar("A")
  let st1 = le_ok(le_typedef(empty_kernel_state(), "box", ["A"], "rep_box", a))
  assert_true(
    ty_eq(
      ks_const_schema(st1, "rep_box").unwrap(),
      fun_ty(mk_tyapp("box", [a]), a),
    ),
  )
}

///|
test "TypeDefGate.abs_ty: abs : repTy -> k(α)" {
  let a = mk_tyvar("A")
  let st1 = le_ok(le_typedef(empty_kernel_state(), "box", ["A"], "rep_box", a))
  assert_true(
    ty_eq(
      ks_const_schema(st1, "Abs_box").unwrap(),
      fun_ty(a, mk_tyapp("box", [a])),
    ),
  )
}

///|
test "TypeDefGate.closed: every annotation type variable is a parameter" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  assert_true(
    le_typedef(st, "t", [], "rep_t", a) is Err(TypeWitnessArityMismatch),
  )
  // A binder annotation counts too.
  let ghost = le_refl_pred(mk_tyvar("B"))
  let x = mk_var("x", bool_ty())
  let pred = mk_abs(x, le_eq(ghost, ghost))
  let witness = le_ok(refl_checked(st, ghost))
  assert_true(
    ks_register_type_definition(st, "t", [], "rep_t", pred, witness)
    is Err(TypeWitnessArityMismatch),
  )
}

///|
test "TypeDefGate.k_fresh: the type constructor is new" {
  let st0 = empty_kernel_state()
  for tycon in ["bool", "fun"] {
    assert_true(
      le_typedef(st0, tycon, [], "rep_t", bool_ty())
      is Err(TypeConstructorAlreadyExists),
    )
  }
  let st1 = le_ok(le_typedef(st0, "u", [], "rep_u", bool_ty()))
  assert_true(
    le_typedef(st1, "u", [], "rep_u2", bool_ty())
    is Err(TypeConstructorAlreadyExists),
  )
}

///|
test "TypeDefGate.rep_ne_abs: rep and abs are different constants" {
  assert_true(
    le_typedef(empty_kernel_state(), "u", [], "Abs_u", bool_ty())
    is Err(InvalidTypeAbsName),
  )
}

///|
test "TypeDefGate.rep_fresh: the representation name is new" {
  let st0 = empty_kernel_state()
  let st1 = le_ok(ks_add_const(st0, "rep_u", bool_ty()))
  assert_true(
    le_typedef(st1, "u", [], "rep_u", bool_ty())
    is Err(TypeRepresentationAlreadyExists),
  )
}

///|
test "TypeDefGate.abs_fresh: the abstraction name is new" {
  let st0 = empty_kernel_state()
  let st1 = le_ok(ks_add_const(st0, "Abs_u", bool_ty()))
  assert_true(
    le_typedef(st1, "u", [], "rep_u", bool_ty())
    is Err(TypeAbstractionAlreadyExists),
  )
}

///|
test "HistoryDerivation.typedef: requires a hypothesis-free proof of P w" {
  let st = empty_kernel_state()
  let bool = bool_ty()
  let pred = le_refl_pred(bool)
  let p = mk_var("p", bool)
  let with_hyp = le_ok(add_assum_checked(st, p, le_refl_witness(st, bool)))
  assert_true(
    ks_register_type_definition(st, "t", [], "rep_t", pred, with_hyp)
    is Err(InvalidTypeWitness),
  )
  let other = le_ok(refl_checked(st, pred))
  assert_true(
    ks_register_type_definition(st, "t", [], "rep_t", pred, other) is Err(_),
  )
}

///|
fn le_typedef_laws() -> (KernelState, Term, Term, Term, HolType, HolType) {
  let a = mk_tyvar("A")
  let st = le_ok(le_typedef(empty_kernel_state(), "box", ["A"], "rep_box", a))
  let new_ty = mk_tyapp("box", [a])
  let rep = le_ok(ks_mk_const(st, "rep_box"))
  let abs = le_ok(ks_mk_const(st, "Abs_box"))
  (st, rep, abs, le_refl_pred(a), new_ty, a)
}

///|
test "TypeDefLaw.absRep: ⊢ Abs (Rep a) = a" {
  let (st, rep, abs, _, new_ty, _) = le_typedef_laws()
  let (th, _, _) = le_ok(ks_typedef_contract(st, "box"))
  let a = mk_var("a", new_ty)
  assert_true(le_concl_is(th, le_eq(mk_comb(abs, mk_comb(rep, a)), a)))
  assert_true(le_hyps_are(th, []))
  assert_true(thm_is_admissible(st, th))
}

///|
test "TypeDefLaw.repRange: ⊢ P (Rep a)" {
  // Lean states `P.app (Rep a)`; the kernel publishes its beta-reduct.
  let (st, rep, _, _, new_ty, _) = le_typedef_laws()
  let (_, th, _) = le_ok(ks_typedef_contract(st, "box"))
  let rep_a = mk_comb(rep, mk_var("a", new_ty))
  assert_true(le_concl_is(th, le_eq(rep_a, rep_a)))
  assert_true(le_hyps_are(th, []))
  assert_true(thm_is_admissible(st, th))
}

///|
test "TypeDefLaw.repAbs: P r ⊢ Rep (Abs r) = r" {
  let (st, rep, abs, _, _, rep_ty) = le_typedef_laws()
  let (_, _, th) = le_ok(ks_typedef_contract(st, "box"))
  let r = mk_var("r", rep_ty)
  assert_true(le_concl_is(th, le_eq(mk_comb(rep, mk_comb(abs, r)), r)))
  assert_true(le_hyps_are(th, [le_eq(r, r)]))
  assert_true(thm_is_admissible(st, th))
}

///|
test "HistoryDerivation.weaken: older theorems stay admissible after a step" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let th = le_ok(refl_checked(st0, le_refl_pred(a)))
  let (st1, def_th) = le_ok(
    ks_define_const_thm(st0, "d", bool_ty(), le_closed_term(bool_ty())),
  )
  let st2 = le_ok(le_typedef(st1, "u", [], "rep_u", bool_ty()))
  assert_true(thm_is_admissible(st1, th))
  assert_true(thm_is_admissible(st2, th))
  assert_true(thm_is_admissible(st2, def_th))
}
