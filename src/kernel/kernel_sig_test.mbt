///|
fn[T] expect_ok_sig(res : Result[T, SigError]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn[T, E] expect_ok_any_sig_test(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn type_witness_bundle(name : String) -> (Term, Thm) {
  let x = mk_var(name, bool_ty())
  let id = mk_abs(x, x)
  let pred = expect_ok_any_sig_test(mk_eq(id, id))
  let witness = expect_ok_any_sig_test(refl_checked(empty_kernel_state(), id))
  (pred, witness)
}

///|
fn poly_type_witness_bundle() -> (Term, Thm) {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let id = mk_abs(x, x)
  let pred = expect_ok_any_sig_test(mk_eq(id, id))
  let witness = expect_ok_any_sig_test(refl_checked(empty_kernel_state(), id))
  (pred, witness)
}

///|
test "sig rejects reserved symbol insertion" {
  let sig0 = empty_sig()
  assert_true(
    sig_add_const_idempotent_e(sig0, "=", bool_ty()) is Err(ReservedSymbol),
  )
  assert_true(
    sig_add_const_idempotent_e(sig0, "=", mk_tyvar("A")) is Err(ReservedSymbol),
  )
}

///|
test "sig supports lexical shadowing and pop restoration" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let sig1 = expect_ok_sig(sig_add_const_idempotent_e(empty_sig(), "C", a))
  let outer_id = sig_lookup_const_id(sig1, "C")
  assert_true(outer_id is Some(_))
  let sig2 = sig_push_scope(sig1)
  let sig3 = expect_ok_sig(sig_add_const_idempotent_e(sig2, "C", b))
  assert_true(sig_lookup_const(sig3, "C") is Some(TyVal("B")))
  let inner_id = sig_lookup_const_id(sig3, "C")
  assert_true(inner_id is Some(_))
  match (outer_id, inner_id) {
    (Some(oid), Some(iid)) => assert_false(oid == iid)
    _ => assert_false(true)
  }
  let sig4 = expect_ok_sig(sig_pop_scope_e(sig3))
  assert_true(sig_lookup_const(sig4, "C") is Some(TyVal("A")))
  assert_true(sig_lookup_const_id(sig4, "C") == outer_id)
}

///|
test "sig supports principal schema instantiation checks" {
  let a = mk_tyvar("A")
  let sig0 = empty_sig()
  let sig1 = expect_ok_sig(sig_add_const_idempotent_e(sig0, "id", fun_ty(a, a)))
  let bool = bool_ty()

  let ok_inst = sig_mk_const_instance_e(sig1, "id", fun_ty(bool, bool))
  assert_true(ok_inst is Ok(Const("id", _)))

  assert_true(
    sig_mk_const_instance_e(sig1, "id", fun_ty(bool, a))
    is Err(InvalidConstInstance),
  )
}

///|
test "kernel state enforces DefHeads monotonicity across pop" {
  let st0 = expect_ok_sig(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let p = mk_const("P", bool_ty())
  let (st1, _) = expect_ok_sig(ks_define_const(st0, "q", bool_ty(), p))
  assert_true(ks_has_def_head(st1, "q"))

  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig(ks_pop_scope(st2))
  assert_true(ks_has_def_head(st3, "q"))

  let out = ks_define_const(st3, "q", bool_ty(), p)
  assert_true(out is Err(DefinitionAlreadyExists))
}

///|
test "kernel state rejects local const shadowing of def heads" {
  let st0 = expect_ok_sig(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let p = mk_const("P", bool_ty())
  let (st1, _) = expect_ok_sig(ks_define_const(st0, "q", bool_ty(), p))
  let st2 = ks_push_scope(st1)
  assert_true(ks_add_const(st2, "q", bool_ty()) is Err(DefinitionAlreadyExists))
  assert_true(
    ks_add_const(st2, "q", mk_tyvar("A")) is Err(DefinitionAlreadyExists),
  )
}

///|
test "ks_define_const_thm yields empty-hyp definition theorem" {
  let st0 = expect_ok_sig(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let p = mk_const("P", bool_ty())
  let (st1, def_th) = expect_ok_sig(ks_define_const_thm(st0, "q", bool_ty(), p))
  assert_true(ks_has_def_head(st1, "q"))
  assert_eq(thm_hyp_count(def_th), 0)
  assert_true(dest_eq(expect_ok_any_sig_test(thm_concl(def_th))) is Ok((_, _)))
}

///|
test "ks_define_const enforces closedness and acyclic side conditions" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  assert_true(ks_define_const(st0, "d", a, x) is Err(DefinitionNotClosed))

  let bool = bool_ty()
  let c_rhs = mk_const("self", bool)
  assert_true(
    ks_define_const(st0, "self", bool, c_rhs) is Err(DefinitionIsCyclic),
  )
}

///|
test "ks_define_const rejects transitive cycles across deferred heads" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_sig(ks_add_const(st1, "b", bool))
  let b_term = mk_const("b", bool)
  let (st3, _) = expect_ok_sig(ks_define_const(st2, "a", bool, b_term))
  let st4 = ks_push_scope(st3)
  let a_term = mk_const("a", bool)
  assert_true(
    ks_define_const(st4, "b", bool, a_term) is Err(DefinitionIsCyclic),
  )
}

///|
test "ks_define_const rejects reserved symbol and type mismatch" {
  let st0 = expect_ok_sig(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let p = mk_const("P", bool_ty())
  assert_true(ks_define_const(st0, "=", bool_ty(), p) is Err(ReservedSymbol))

  let a = mk_tyvar("A")
  assert_true(ks_define_const(st0, "k", a, p) is Err(TypeMismatch))
}

///|
test "ks_define_const rejects ghost type variables in rhs term" {
  let st0 = expect_ok_sig(
    ks_add_const(
      expect_ok_sig(
        ks_add_const(
          empty_kernel_state(),
          "pred",
          fun_ty(mk_tyvar("A"), bool_ty()),
        ),
      ),
      "c",
      mk_tyvar("A"),
    ),
  )
  let a = mk_tyvar("A")
  let pred = mk_const("pred", fun_ty(a, bool_ty()))
  let c = mk_const("c", a)
  let rhs = mk_comb(pred, c)
  assert_true(
    ks_define_const(st0, "g", bool_ty(), rhs) is Err(GhostTypeVariable),
  )
}

///|
test "ks_define_const rejects rhs with unknown or invalid const instances" {
  let st0 = empty_kernel_state()
  let u = mk_const("U", bool_ty())
  assert_true(ks_define_const(st0, "q", bool_ty(), u) is Err(InvalidConstRhs))

  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st1 = expect_ok_sig(ks_add_const(st0, "id", fun_ty(a, a)))
  let bad_id_inst = mk_const("id", fun_ty(bool, a))
  assert_true(
    ks_define_const(st1, "q2", fun_ty(bool, a), bad_id_inst)
    is Err(InvalidConstRhs),
  )
}

///|
test "type definition registration is fail-closed without witness" {
  let st0 = empty_kernel_state()
  let (pred_p, _) = type_witness_bundle("W_bad")
  let bad_witness = expect_ok_any_sig_test(assume_checked(st0, pred_p))
  assert_true(
    ks_register_type_definition(
      st0,
      "newty",
      ["A"],
      "RepBadW",
      pred_p,
      bad_witness,
    )
    is Err(InvalidTypeWitness),
  )
  let x = mk_var("x", bool_ty())
  let open_pred = expect_ok_any_sig_test(mk_eq(x, x))
  let open_witness = expect_ok_any_sig_test(refl_checked(st0, x))
  assert_true(
    ks_register_type_definition(
      st0,
      "newty",
      ["A"],
      "RepOpenPred",
      open_pred,
      open_witness,
    )
    is Err(InvalidTypePredicate),
  )
  let st_with_w = expect_ok_sig(ks_add_const(st0, "W", bool_ty()))
  let unknown_c = expect_ok_any_sig_test(ks_mk_const(st_with_w, "W"))
  let unknown_const_pred = expect_ok_any_sig_test(mk_eq(unknown_c, unknown_c))
  let unknown_const_witness = expect_ok_any_sig_test(
    refl_checked(st_with_w, unknown_c),
  )
  assert_true(
    ks_register_type_definition(
      st0,
      "newty",
      ["A"],
      "RepUnknown",
      unknown_const_pred,
      unknown_const_witness,
    )
    is Err(InvalidTypePredicate),
  )
  assert_true(
    ks_register_type_definition(
      st0,
      "newty",
      ["A"],
      "RepMismatch",
      pred_p,
      unknown_const_witness,
    )
    is Err(InvalidTypeWitness),
  )
  let st_known = expect_ok_sig(ks_add_const(st0, "W", bool_ty()))
  assert_true(
    ks_register_type_definition(
      st_known,
      "newty",
      ["A"],
      "RepKnown",
      unknown_const_pred,
      unknown_const_witness,
    )
    is Ok(_),
  )
  let st_shadow = ks_push_scope(st_known)
  let st_shadow2 = expect_ok_sig(ks_add_const(st_shadow, "W", bool_ty()))
  let drifted_witness = expect_ok_any_sig_test(
    refl_checked(st_shadow2, mk_const("W", bool_ty())),
  )
  let bound_known_witness = expect_ok_any_sig_test(
    thm_bind_const_ids(st_known, unknown_const_witness),
  )
  assert_true(
    ks_register_type_definition(
      st_known,
      "newty_drift",
      ["A"],
      "RepKnownDrift",
      unknown_const_pred,
      drifted_witness,
    )
    is Err(InvalidTypeWitness),
  )
  assert_true(
    ks_register_type_definition(
      st_known,
      "newty_bound",
      ["A"],
      "RepKnownMismatch",
      pred_p,
      bound_known_witness,
    )
    is Err(TypeWitnessPredicateMismatch),
  )
  assert_true(
    ks_register_type_definition(
      st_known,
      "newty",
      ["A"],
      "RepKnownBound",
      unknown_const_pred,
      bound_known_witness,
    )
    is Ok(_),
  )
  let (pred, witness) = type_witness_bundle("W")
  assert_true(
    ks_register_type_definition(st0, "newty", ["A"], "RepW", pred, witness)
    is Ok(_),
  )
  let st1 = expect_ok_sig(
    ks_register_type_definition(st0, "newty", ["A"], "RepW1", pred, witness),
  )
  assert_true(ks_has_type_witness(st1, "newty", 1))
}

///|
test "type definition registration rejects const-id drifted witness" {
  let bool = bool_ty()
  let st0 = expect_ok_sig(ks_add_const(empty_kernel_state(), "W", bool))
  let w = mk_const("W", bool)
  let pred = expect_ok_any_sig_test(mk_eq(w, w))
  let witness = expect_ok_any_sig_test(refl_checked(st0, w))
  assert_true(
    ks_register_type_definition(st0, "w0", [], "RepW0", pred, witness) is Ok(_),
  )

  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_sig(ks_add_const(st1, "W", bool))
  assert_true(
    ks_register_type_definition(st2, "w1", [], "RepW1", pred, witness)
    is Err(InvalidTypeWitness),
  )
}

///|
test "type definition registration validates tycon name and arity" {
  let st0 = empty_kernel_state()
  let (pred, witness) = type_witness_bundle("W_arity")
  assert_true(
    ks_register_type_definition(st0, "", ["A"], "RepArity0", pred, witness)
    is Err(InvalidTypeArity),
  )
  assert_true(
    ks_register_type_definition(st0, "newty", [""], "RepArity1", pred, witness)
    is Err(InvalidTypeParams),
  )
  assert_true(
    ks_register_type_definition(st0, "newty0", [], "RepArity2", pred, witness)
    is Ok(_),
  )
}

///|
test "type definition registration checks witness type vars against arity" {
  let st0 = empty_kernel_state()
  let (poly_pred, poly_witness) = poly_type_witness_bundle()
  assert_true(
    ks_register_type_definition(
      st0,
      "mono",
      [],
      "RepMono",
      poly_pred,
      poly_witness,
    )
    is Err(TypeWitnessArityMismatch),
  )
  assert_true(
    ks_register_type_definition(
      st0,
      "poly1",
      ["A"],
      "RepPoly",
      poly_pred,
      poly_witness,
    )
    is Ok(_),
  )
}

///|
test "type definition registration rejects duplicate type params" {
  let st0 = empty_kernel_state()
  let (poly_pred, poly_witness) = poly_type_witness_bundle()
  assert_true(
    ks_register_type_definition(
      st0,
      "dup",
      ["A", "A"],
      "RepDup",
      poly_pred,
      poly_witness,
    )
    is Err(InvalidTypeParams),
  )
}

///|
test "type definition registration validates rep name freshness" {
  let st0 = empty_kernel_state()
  let (pred, witness) = type_witness_bundle("W_rep")
  assert_true(
    ks_register_type_definition(st0, "repbad0", [], "", pred, witness)
    is Err(InvalidTypeRepName),
  )
  assert_true(
    ks_register_type_definition(st0, "repbad1", [], "=", pred, witness)
    is Err(InvalidTypeRepName),
  )
  let st1 = expect_ok_sig(
    ks_register_type_definition(st0, "repfresh", [], "RepFresh", pred, witness),
  )
  assert_true(
    ks_register_type_definition(st1, "repfresh2", [], "RepFresh", pred, witness)
    is Err(TypeRepresentationAlreadyExists),
  )
  let st2 = expect_ok_sig(ks_add_const(st0, "RepC", bool_ty()))
  assert_true(
    ks_register_type_definition(st2, "repfresh3", [], "RepC", pred, witness)
    is Err(TypeRepresentationAlreadyExists),
  )
}

///|
test "type representation heads cannot be reused as constants" {
  let st0 = empty_kernel_state()
  let (pred, witness) = type_witness_bundle("W_rep_guard")
  let st1 = expect_ok_sig(
    ks_register_type_definition(st0, "repguard", [], "RepGuard", pred, witness),
  )
  let bool = bool_ty()
  let x = mk_var("x", bool)
  assert_true(
    ks_add_const(st1, "RepGuard", bool) is Err(TypeRepresentationAlreadyExists),
  )
  assert_true(
    ks_define_const(st1, "RepGuard", bool, x)
    is Err(TypeRepresentationAlreadyExists),
  )
  let st2 = ks_push_scope(st1)
  assert_true(
    ks_add_const(st2, "RepGuard", bool) is Err(TypeRepresentationAlreadyExists),
  )
}

///|
test "type definition registration enforces tycon freshness" {
  let st0 = empty_kernel_state()
  let (pred, witness) = type_witness_bundle("W_fresh")
  let st1 = expect_ok_sig(
    ks_register_type_definition(st0, "fresh", ["A"], "RepFresh0", pred, witness),
  )
  assert_true(
    ks_register_type_definition(st1, "fresh", ["A"], "RepFresh1", pred, witness)
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(
      st1,
      "fresh",
      ["A", "B"],
      "RepFresh2",
      pred,
      witness,
    )
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(st0, "bool", [], "RepBool", pred, witness)
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(st0, "fun", ["A", "B"], "RepFun", pred, witness)
    is Err(TypeConstructorAlreadyExists),
  )
}

///|
test "state admissible type checks honor witnesses and builtin tycons" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool_fun = fun_ty(a, bool_ty())
  assert_true(ks_type_is_admissible(st0, bool_fun))

  let custom = mk_tyapp("custom", [a])
  assert_false(ks_type_is_admissible(st0, custom))

  let (pred, witness) = type_witness_bundle("W2")
  let st1 = expect_ok_sig(
    ks_register_type_definition(
      st0,
      "custom",
      ["A"],
      "RepCustom",
      pred,
      witness,
    ),
  )
  assert_true(ks_type_is_admissible(st1, custom))
  assert_true(ks_type_subst_is_admissible(st1, [("A", custom)]))
  assert_false(ks_type_subst_is_admissible(st0, [("A", custom)]))
}

///|
test "kernel state exposes stable const ids for lookups" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let st1 = expect_ok_sig(ks_add_const(st0, "k", a))
  let id1 = ks_lookup_const_id(st1, "k")
  assert_true(id1 is Some(_))
  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig(ks_add_const(st2, "k", a))
  let id2 = ks_lookup_const_id(st3, "k")
  assert_true(id2 is Some(_))
  match (id1, id2) {
    (Some(v1), Some(v2)) => assert_false(v1 == v2)
    _ => assert_false(true)
  }
}

///|
test "kernel state keeps const ids monotone across pop and re-add" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let st1 = expect_ok_sig(ks_add_const(st0, "k", a))
  let id1 = ks_lookup_const_id(st1, "k")
  assert_true(id1 is Some(_))

  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig(ks_add_const(st2, "k", a))
  let id2 = ks_lookup_const_id(st3, "k")
  assert_true(id2 is Some(_))

  let st4 = expect_ok_sig(ks_pop_scope(st3))
  let st5 = ks_push_scope(st4)
  let st6 = expect_ok_sig(ks_add_const(st5, "k", a))
  let id3 = ks_lookup_const_id(st6, "k")
  assert_true(id3 is Some(_))

  match (id1, id2, id3) {
    (Some(v1), Some(v2), Some(v3)) => {
      assert_false(v1 == v2)
      assert_false(v2 == v3)
      assert_false(v1 == v3)
    }
    _ => assert_false(true)
  }
}

///|
test "kernel state exposes schema-checked instance constructor" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st1 = expect_ok_sig(ks_add_const(st0, "id", fun_ty(a, a)))
  assert_true(ks_mk_const(st1, "id") is Ok(_))
  assert_true(ks_mk_const(st1, "missing") is Err(UnknownConst))
  assert_true(ks_mk_const_instance(st1, "id", fun_ty(bool, bool)) is Ok(_))
  assert_true(
    ks_mk_const_instance(st1, "id", fun_ty(bool, a))
    is Err(InvalidConstInstance),
  )
}
