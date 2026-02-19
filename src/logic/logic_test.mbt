///|
fn[T, E] expect_ok_logic(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn closed_eq_witness_term_logic(ty : @kernel.HolType) -> @kernel.Term {
  let x = @kernel.mk_var("_w_logic", ty)
  let body = expect_ok_logic(@kernel.mk_eq(x, x))
  let pred = @kernel.mk_abs(x, body)
  @kernel.mk_comb(
    @kernel.mk_const(
      "@",
      @kernel.fun_ty(@kernel.fun_ty(ty, @kernel.bool_ty()), ty),
    ),
    pred,
  )
}

///|
fn typedef_bundle_logic(
  ty : @kernel.HolType,
  name : String,
) -> (@kernel.Term, @kernel.Thm) {
  let x = @kernel.mk_var(name, ty)
  let body = expect_ok_logic(@kernel.mk_eq(x, x))
  let pred = @kernel.mk_abs(x, body)
  let witness = expect_ok_logic(
    logic_refl(@kernel.empty_kernel_state(), closed_eq_witness_term_logic(ty)),
  )
  (pred, witness)
}

///|
test "logic wrappers call kernel rules" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let st = expect_ok_logic(@kernel.ks_add_const(st0, "P", bool))
  let p = expect_ok_logic(@kernel.ks_mk_const(st, "P"))
  let th_assume = logic_assume(st, p)
  assert_true(th_assume is Ok(_))

  let x = @kernel.mk_var("x", @kernel.mk_tyvar("A"))
  let th_refl = logic_refl(st, x)
  assert_true(th_refl is Ok(_))
}

///|
test "logic checked wrappers reject inadmissible constants and id drift" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let p = @kernel.mk_const("P", bool)
  assert_true(logic_assume(st0, p) is Err(@kernel.TypeMismatch))

  let st1 = expect_ok_logic(@kernel.ks_add_const(st0, "P", bool))
  let p1 = expect_ok_logic(@kernel.ks_mk_const(st1, "P"))
  assert_true(logic_assume(st1, p1) is Ok(_))

  let th_refl = expect_ok_logic(logic_refl(st1, p1))
  let st2 = @kernel.ks_push_scope(st1)
  let st3 = expect_ok_logic(@kernel.ks_add_const(st2, "P", bool))
  assert_true(
    logic_trans(st3, th_refl, th_refl) is Err(@kernel.InvalidInstantiation),
  )

  let p3 = expect_ok_logic(@kernel.ks_mk_const(st3, "P"))
  let drifted_refl = expect_ok_logic(logic_refl(st3, p3))
  assert_true(
    logic_trans(st1, drifted_refl, drifted_refl)
    is Err(@kernel.InvalidInstantiation),
  )
}

///|
test "logic trans wrapper composes equality theorems" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let z = @kernel.mk_var("z", a)

  let th1 = expect_ok_logic(
    logic_assume(st, expect_ok_logic(@kernel.mk_eq(x, y))),
  )
  let th2 = expect_ok_logic(
    logic_assume(st, expect_ok_logic(@kernel.mk_eq(y, z))),
  )
  assert_true(logic_trans(st, th1, th2) is Ok(_))
}

///|
test "logic extension wrappers provide typedef, spec, and cert flow" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let (td_pred, td_witness) = typedef_bundle_logic(bool, "x_td_logic")
  let st1 = expect_ok_logic(
    logic_register_typedef(
      st0,
      "logicty",
      [],
      "RepLogicTy",
      td_pred,
      td_witness,
    ),
  )
  assert_true(logic_typedef_contract(st1, "logicty") is Ok((_, _, _)))

  let x = @kernel.mk_var("x_spec_logic", bool)
  let spec_pred = @kernel.mk_abs(x, expect_ok_logic(@kernel.mk_eq(x, x)))
  let spec_witness = expect_ok_logic(
    logic_refl(st1, closed_eq_witness_term_logic(bool)),
  )
  let (st2, spec_th) = expect_ok_logic(
    logic_specify_const(st1, "c_logic", bool, spec_pred, spec_witness),
  )
  assert_eq(@kernel.thm_hyp_count(spec_th), 0)
  assert_true(logic_extension_cert_count(st2) == 3)
  assert_true(
    logic_extension_cert_at(st2, 0) is Some((@kernel.TypeDefOK, _, _)),
  )
  assert_true(logic_extension_cert_at(st2, 1) is Some((@kernel.DefOK, _, _)))
  assert_true(logic_extension_cert_at(st2, 2) is Some((@kernel.SpecOK, _, _)))
}

///|
test "logic infinity anchor and conservativity replay wrappers work" {
  let bool = @kernel.bool_ty()
  let st0 = expect_ok_logic(
    @kernel.ks_add_const(@kernel.empty_kernel_state(), "P", bool),
  )
  let n = @kernel.mk_var("n", @kernel.ind_ty())
  let anchor = expect_ok_logic(logic_refl(st0, n))
  let st1 = expect_ok_logic(logic_register_ind_infinity_anchor(st0, anchor))
  assert_true(logic_ind_infinity_anchor(st1) is Ok(_))

  let p = @kernel.mk_const("P", bool)
  let th_old = expect_ok_logic(logic_refl(st1, p))
  assert_true(logic_conservative_replay_ok(st0, st1, th_old))
}

///|
test "logic spec wrapper fails on non-empty witness assumptions" {
  let st0 = @kernel.empty_kernel_state()
  let x = @kernel.mk_var("x", @kernel.bool_ty())
  let pred_body = expect_ok_logic(@kernel.mk_eq(x, x))
  let pred = @kernel.mk_abs(x, pred_body)
  let bad_w = expect_ok_logic(logic_assume(st0, pred_body))
  assert_true(
    logic_specify_const(st0, "bad_logic_spec", @kernel.bool_ty(), pred, bad_w)
    is Err(@kernel.InvalidSpecificationWitness),
  )
}

///|
test "logic typedef wrapper enforces witness and freshness guards" {
  let st0 = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let x = @kernel.mk_var("x_td_guard", bool)
  let pred_body = expect_ok_logic(@kernel.mk_eq(x, x))
  let pred = @kernel.mk_abs(x, pred_body)

  let bad_w = expect_ok_logic(logic_assume(st0, pred_body))
  assert_true(
    logic_register_typedef(st0, "ty_guard", [], "RepTyGuard", pred, bad_w)
    is Err(@kernel.InvalidTypeWitness),
  )

  let good_w = expect_ok_logic(
    logic_refl(st0, closed_eq_witness_term_logic(bool)),
  )
  let st1 = expect_ok_logic(
    logic_register_typedef(st0, "ty_guard", [], "RepTyGuard", pred, good_w),
  )
  assert_true(
    logic_register_typedef(st1, "ty_guard2", [], "RepTyGuard", pred, good_w)
    is Err(@kernel.TypeRepresentationAlreadyExists),
  )
  assert_true(
    logic_register_typedef(st1, "ty_guard", [], "RepTyGuard2", pred, good_w)
    is Err(@kernel.TypeConstructorAlreadyExists),
  )
}

///|
test "logic typedef contract wrapper is fail-closed for missing tycon" {
  let st0 = @kernel.empty_kernel_state()
  assert_true(
    logic_typedef_contract(st0, "missing_tycon")
    is Err(@kernel.MissingTypeDefinitionContract),
  )
}

///|
test "logic spec wrapper enforces typevar and witness constraints" {
  let st0 = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let b = @kernel.mk_tyvar("B")
  let x = @kernel.mk_var("x_spec_guard", a)
  let u = @kernel.mk_var("u_spec_guard", b)
  let id_b = @kernel.mk_abs(u, u)
  let leak_body = expect_ok_logic(@kernel.mk_eq(id_b, id_b))
  let leak_pred = @kernel.mk_abs(x, leak_body)
  let leak_w = expect_ok_logic(logic_refl(st0, id_b))
  assert_true(
    logic_specify_const(st0, "spec_leak", a, leak_pred, leak_w)
    is Err(@kernel.SpecificationTypeVarLeak),
  )

  let y = @kernel.mk_var("y_spec_guard", @kernel.bool_ty())
  let dom_pred = @kernel.mk_abs(y, expect_ok_logic(@kernel.mk_eq(y, y)))
  let dom_w = expect_ok_logic(logic_refl(st0, y))
  assert_true(
    logic_specify_const(st0, "spec_dom", a, dom_pred, dom_w)
    is Err(@kernel.InvalidSpecificationPredicate),
  )

  let st1 = expect_ok_logic(
    @kernel.ks_add_const(st0, "W_SPEC", @kernel.bool_ty()),
  )
  let w = @kernel.mk_const("W_SPEC", @kernel.bool_ty())
  let z = @kernel.mk_var("z_spec_guard", @kernel.bool_ty())
  let drift_pred = @kernel.mk_abs(z, expect_ok_logic(@kernel.mk_eq(w, w)))
  let drift_w = expect_ok_logic(logic_refl(st1, w))
  assert_true(
    logic_specify_const(
      st0,
      "spec_drift",
      @kernel.bool_ty(),
      drift_pred,
      drift_w,
    )
    is Err(@kernel.InvalidSpecificationWitness),
  )
}

///|
test "logic infinity anchor wrapper enforces single-assignment and shape" {
  let st0 = @kernel.empty_kernel_state()
  assert_true(
    logic_ind_infinity_anchor(st0) is Err(@kernel.MissingInfinityAnchor),
  )

  let b = @kernel.mk_var("b_anchor_guard", @kernel.bool_ty())
  let bad_anchor = expect_ok_logic(logic_refl(st0, b))
  assert_true(
    logic_register_ind_infinity_anchor(st0, bad_anchor)
    is Err(@kernel.InvalidInfinityAnchor),
  )

  let n = @kernel.mk_var("n_anchor_guard", @kernel.ind_ty())
  let good_anchor = expect_ok_logic(logic_refl(st0, n))
  let st1 = expect_ok_logic(
    logic_register_ind_infinity_anchor(st0, good_anchor),
  )
  assert_true(logic_ind_infinity_anchor(st1) is Ok(_))
  assert_true(
    logic_register_ind_infinity_anchor(st1, good_anchor)
    is Err(@kernel.InvalidInfinityAnchor),
  )
}

///|
test "logic conservative replay rejects new-language theorems" {
  let bool = @kernel.bool_ty()
  let st0 = expect_ok_logic(
    @kernel.ks_add_const(@kernel.empty_kernel_state(), "P0", bool),
  )
  let x = @kernel.mk_var("x_cons_guard", bool)
  let pred = @kernel.mk_abs(x, expect_ok_logic(@kernel.mk_eq(x, x)))
  let witness = expect_ok_logic(
    logic_refl(st0, closed_eq_witness_term_logic(bool)),
  )
  let (st1, _) = expect_ok_logic(
    logic_specify_const(st0, "c_cons_guard", bool, pred, witness),
  )

  let p0 = @kernel.mk_const("P0", bool)
  let c0 = @kernel.mk_const("c_cons_guard", bool)
  let th_old = expect_ok_logic(logic_refl(st1, p0))
  let th_new = expect_ok_logic(logic_refl(st1, c0))
  assert_true(logic_conservative_replay_ok(st0, st1, th_old))
  assert_false(logic_conservative_replay_ok(st0, st1, th_new))
}
