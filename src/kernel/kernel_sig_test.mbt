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
fn type_witness_thm(name : String) -> Thm {
  let x = mk_var(name, bool_ty())
  expect_ok_any_sig_test(refl(mk_abs(x, x)))
}

///|
fn poly_type_witness_thm() -> Thm {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  expect_ok_any_sig_test(refl(mk_abs(x, x)))
}

///|
test "sig rejects reserved symbol insertion" {
  let sig0 = empty_sig()
  assert_true(sig_add_const(sig0, "=", bool_ty()) is None)
  assert_true(
    sig_add_const_idempotent_e(sig0, "=", bool_ty()) is Err(ReservedSymbol),
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

  let ok_inst = sig_mk_const_instance(sig1, "id", fun_ty(bool, bool))
  assert_true(ok_inst is Some(Const("id", _)))

  let bad_inst = sig_mk_const_instance(sig1, "id", fun_ty(bool, a))
  assert_true(bad_inst is None)
  assert_true(
    sig_mk_const_instance_e(sig1, "id", fun_ty(bool, a))
    is Err(InvalidConstInstance),
  )
}

///|
test "kernel state enforces DefHeads monotonicity across pop" {
  let st0 = empty_kernel_state()
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
test "ks_define_const_thm yields empty-hyp definition theorem" {
  let st0 = empty_kernel_state()
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
test "ks_define_const rejects reserved symbol and type mismatch" {
  let st0 = empty_kernel_state()
  let p = mk_const("P", bool_ty())
  assert_true(ks_define_const(st0, "=", bool_ty(), p) is Err(ReservedSymbol))

  let a = mk_tyvar("A")
  assert_true(ks_define_const(st0, "k", a, p) is Err(TypeMismatch))
}

///|
test "ks_define_const rejects ghost type variables in rhs term" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let pred = mk_const("pred", fun_ty(a, bool_ty()))
  let c = mk_const("c", a)
  let rhs = mk_comb(pred, c)
  assert_true(
    ks_define_const(st0, "g", bool_ty(), rhs) is Err(GhostTypeVariable),
  )
}

///|
test "type definition registration is fail-closed without witness" {
  let st0 = empty_kernel_state()
  let bad_witness = expect_ok_any_sig_test(assume(mk_const("P", bool_ty())))
  let open_witness = expect_ok_any_sig_test(refl(mk_var("x", bool_ty())))
  let unknown_const_witness = expect_ok_any_sig_test(
    refl(mk_const("W", bool_ty())),
  )
  assert_true(
    ks_register_type_definition(st0, "newty", 1, bad_witness)
    is Err(InvalidTypeWitness),
  )
  assert_true(
    ks_register_type_definition(st0, "newty", 1, open_witness)
    is Err(InvalidTypeWitness),
  )
  assert_true(
    ks_register_type_definition(st0, "newty", 1, unknown_const_witness)
    is Err(InvalidTypeWitness),
  )
  let st_known = expect_ok_sig(ks_add_const(st0, "W", bool_ty()))
  assert_true(
    ks_register_type_definition(st_known, "newty", 1, unknown_const_witness)
    is Ok(_),
  )
  let witness = type_witness_thm("W")
  assert_true(ks_register_type_definition(st0, "newty", 1, witness) is Ok(_))
  let st1 = expect_ok_sig(ks_register_type_definition(st0, "newty", 1, witness))
  assert_true(ks_has_type_witness(st1, "newty", 1))
}

///|
test "type definition registration validates tycon name and arity" {
  let st0 = empty_kernel_state()
  let witness = type_witness_thm("W_arity")
  assert_true(
    ks_register_type_definition(st0, "", 1, witness) is Err(InvalidTypeArity),
  )
  assert_true(
    ks_register_type_definition(st0, "newty", -1, witness)
    is Err(InvalidTypeArity),
  )
  assert_true(ks_register_type_definition(st0, "newty0", 0, witness) is Ok(_))
}

///|
test "type definition registration checks witness type vars against arity" {
  let st0 = empty_kernel_state()
  let poly_witness = poly_type_witness_thm()
  assert_true(
    ks_register_type_definition(st0, "mono", 0, poly_witness)
    is Err(TypeWitnessArityMismatch),
  )
  assert_true(
    ks_register_type_definition(st0, "poly1", 1, poly_witness) is Ok(_),
  )
}

///|
test "type definition registration enforces tycon freshness" {
  let st0 = empty_kernel_state()
  let witness = type_witness_thm("W_fresh")
  let st1 = expect_ok_sig(ks_register_type_definition(st0, "fresh", 1, witness))
  assert_true(
    ks_register_type_definition(st1, "fresh", 1, witness)
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(st1, "fresh", 2, witness)
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(st0, "bool", 0, witness)
    is Err(TypeConstructorAlreadyExists),
  )
  assert_true(
    ks_register_type_definition(st0, "fun", 2, witness)
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

  let witness = type_witness_thm("W2")
  let st1 = expect_ok_sig(
    ks_register_type_definition(st0, "custom", 1, witness),
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
test "kernel state exposes schema-checked instance constructor" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st1 = expect_ok_sig(ks_add_const(st0, "id", fun_ty(a, a)))
  assert_true(ks_mk_const_instance(st1, "id", fun_ty(bool, bool)) is Ok(_))
  assert_true(
    ks_mk_const_instance(st1, "id", fun_ty(bool, a))
    is Err(InvalidConstInstance),
  )
}
