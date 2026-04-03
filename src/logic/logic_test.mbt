///|
using @kernel {
  type HolType,
  type Term,
  type Thm,
  bool_ty,
  empty_kernel_state,
  fun_ty,
  ind_ty,
  ks_add_const,
  ks_mk_const,
  ks_push_scope,
  mk_abs,
  mk_comb,
  mk_const,
  mk_eq,
  mk_tyvar,
  mk_var,
  thm_hyp_count,
}

///|
fn[T, E] expect_ok_logic(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn closed_eq_witness_term_logic(ty : HolType) -> Term {
  let x = mk_var("_w_logic", ty)
  let body = expect_ok_logic(mk_eq(x, x))
  let pred = mk_abs(x, body)
  mk_comb(mk_const("@", fun_ty(fun_ty(ty, bool_ty()), ty)), pred)
}

///|
fn typedef_bundle_logic(ty : HolType, name : String) -> (Term, Thm) {
  let x = mk_var(name, ty)
  let body = expect_ok_logic(mk_eq(x, x))
  let pred = mk_abs(x, body)
  let witness = expect_ok_logic(
    logic_refl(empty_kernel_state(), closed_eq_witness_term_logic(ty)),
  )
  (pred, witness)
}

///|
test "logic wrappers call kernel rules" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st = expect_ok_logic(ks_add_const(st0, "P", bool))
  let p = expect_ok_logic(ks_mk_const(st, "P"))
  let th_assume = logic_assume(st, p)
  assert_true(th_assume is Ok(_))

  let x = mk_var("x", mk_tyvar("A"))
  let th_refl = logic_refl(st, x)
  assert_true(th_refl is Ok(_))
}

///|
test "logic checked wrappers reject inadmissible constants and id drift" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let p = mk_const("P", bool)
  assert_true(logic_assume(st0, p) is Err(TypeMismatch))

  let st1 = expect_ok_logic(ks_add_const(st0, "P", bool))
  let p1 = expect_ok_logic(ks_mk_const(st1, "P"))
  assert_true(logic_assume(st1, p1) is Ok(_))

  let th_refl = expect_ok_logic(logic_refl(st1, p1))
  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_logic(ks_add_const(st2, "P", bool))
  assert_true(logic_trans(st3, th_refl, th_refl) is Err(InvalidInstantiation))

  let p3 = expect_ok_logic(ks_mk_const(st3, "P"))
  let drifted_refl = expect_ok_logic(logic_refl(st3, p3))
  assert_true(
    logic_trans(st1, drifted_refl, drifted_refl) is Err(InvalidInstantiation),
  )
}

///|
test "logic trans wrapper composes equality theorems" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)

  let th1 = expect_ok_logic(logic_assume(st, expect_ok_logic(mk_eq(x, y))))
  let th2 = expect_ok_logic(logic_assume(st, expect_ok_logic(mk_eq(y, z))))
  assert_true(logic_trans(st, th1, th2) is Ok(_))
}

///|
test "logic extension wrappers provide typedef, spec, and cert flow" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
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

  let x = mk_var("x_spec_logic", bool)
  let spec_pred = mk_abs(x, expect_ok_logic(mk_eq(x, x)))
  let spec_witness = expect_ok_logic(
    logic_refl(st1, closed_eq_witness_term_logic(bool)),
  )
  let (st2, spec_th) = expect_ok_logic(
    logic_specify_const(st1, "c_logic", bool, spec_pred, spec_witness),
  )
  assert_eq(thm_hyp_count(spec_th), 0)
  assert_true(logic_extension_cert_count(st2) == 3)
  assert_true(logic_extension_cert_at(st2, 0) is Some((TypeDefOK, _, _)))
  assert_true(logic_extension_cert_at(st2, 1) is Some((DefOK, _, _)))
  assert_true(logic_extension_cert_at(st2, 2) is Some((SpecOK, _, _)))
}

///|
test "logic infinity anchor and conservativity replay wrappers work" {
  let bool = bool_ty()
  let st0 = expect_ok_logic(ks_add_const(empty_kernel_state(), "P", bool))
  let n = mk_var("n", ind_ty())
  let anchor = expect_ok_logic(logic_refl(st0, n))
  let st1 = expect_ok_logic(logic_register_ind_infinity_anchor(st0, anchor))
  assert_true(logic_ind_infinity_anchor(st1) is Ok(_))

  let p = mk_const("P", bool)
  let th_old = expect_ok_logic(logic_refl(st1, p))
  assert_true(logic_conservative_replay_ok(st0, st1, th_old))
}

///|
test "logic spec wrapper fails on non-empty witness assumptions" {
  let st0 = empty_kernel_state()
  let x = mk_var("x", bool_ty())
  let pred_body = expect_ok_logic(mk_eq(x, x))
  let pred = mk_abs(x, pred_body)
  let bad_w = expect_ok_logic(logic_assume(st0, pred_body))
  assert_true(
    logic_specify_const(st0, "bad_logic_spec", bool_ty(), pred, bad_w)
    is Err(InvalidSpecificationWitness),
  )
}

///|
test "logic typedef wrapper enforces witness and freshness guards" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let x = mk_var("x_td_guard", bool)
  let pred_body = expect_ok_logic(mk_eq(x, x))
  let pred = mk_abs(x, pred_body)

  let bad_w = expect_ok_logic(logic_assume(st0, pred_body))
  assert_true(
    logic_register_typedef(st0, "ty_guard", [], "RepTyGuard", pred, bad_w)
    is Err(InvalidTypeWitness),
  )

  let good_w = expect_ok_logic(
    logic_refl(st0, closed_eq_witness_term_logic(bool)),
  )
  let st1 = expect_ok_logic(
    logic_register_typedef(st0, "ty_guard", [], "RepTyGuard", pred, good_w),
  )
  assert_true(
    logic_register_typedef(st1, "ty_guard2", [], "RepTyGuard", pred, good_w)
    is Err(TypeRepresentationAlreadyExists),
  )
  assert_true(
    logic_register_typedef(st1, "ty_guard", [], "RepTyGuard2", pred, good_w)
    is Err(TypeConstructorAlreadyExists),
  )
}

///|
test "logic typedef contract wrapper is fail-closed for missing tycon" {
  let st0 = empty_kernel_state()
  assert_true(
    logic_typedef_contract(st0, "missing_tycon")
    is Err(MissingTypeDefinitionContract),
  )
}

///|
test "logic spec wrapper enforces typevar and witness constraints" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x_spec_guard", a)
  let u = mk_var("u_spec_guard", b)
  let id_b = mk_abs(u, u)
  let leak_body = expect_ok_logic(mk_eq(id_b, id_b))
  let leak_pred = mk_abs(x, leak_body)
  let leak_w = expect_ok_logic(logic_refl(st0, id_b))
  assert_true(
    logic_specify_const(st0, "spec_leak", a, leak_pred, leak_w)
    is Err(SpecificationTypeVarLeak),
  )

  let y = mk_var("y_spec_guard", bool_ty())
  let dom_pred = mk_abs(y, expect_ok_logic(mk_eq(y, y)))
  let dom_w = expect_ok_logic(logic_refl(st0, y))
  assert_true(
    logic_specify_const(st0, "spec_dom", a, dom_pred, dom_w)
    is Err(InvalidSpecificationPredicate),
  )

  let st1 = expect_ok_logic(ks_add_const(st0, "W_SPEC", bool_ty()))
  let w = mk_const("W_SPEC", bool_ty())
  let z = mk_var("z_spec_guard", bool_ty())
  let drift_pred = mk_abs(z, expect_ok_logic(mk_eq(w, w)))
  let drift_w = expect_ok_logic(logic_refl(st1, w))
  assert_true(
    logic_specify_const(st0, "spec_drift", bool_ty(), drift_pred, drift_w)
    is Err(InvalidSpecificationWitness),
  )
}

///|
test "logic infinity anchor wrapper enforces single-assignment and shape" {
  let st0 = empty_kernel_state()
  assert_true(logic_ind_infinity_anchor(st0) is Err(MissingInfinityAnchor))

  let b = mk_var("b_anchor_guard", bool_ty())
  let bad_anchor = expect_ok_logic(logic_refl(st0, b))
  assert_true(
    logic_register_ind_infinity_anchor(st0, bad_anchor)
    is Err(InvalidInfinityAnchor),
  )

  let n = mk_var("n_anchor_guard", ind_ty())
  let good_anchor = expect_ok_logic(logic_refl(st0, n))
  let st1 = expect_ok_logic(
    logic_register_ind_infinity_anchor(st0, good_anchor),
  )
  assert_true(logic_ind_infinity_anchor(st1) is Ok(_))
  assert_true(
    logic_register_ind_infinity_anchor(st1, good_anchor)
    is Err(InvalidInfinityAnchor),
  )
}

///|
test "logic conservative replay rejects new-language theorems" {
  let bool = bool_ty()
  let st0 = expect_ok_logic(ks_add_const(empty_kernel_state(), "P0", bool))
  let x = mk_var("x_cons_guard", bool)
  let pred = mk_abs(x, expect_ok_logic(mk_eq(x, x)))
  let witness = expect_ok_logic(
    logic_refl(st0, closed_eq_witness_term_logic(bool)),
  )
  let (st1, _) = expect_ok_logic(
    logic_specify_const(st0, "c_cons_guard", bool, pred, witness),
  )

  let p0 = mk_const("P0", bool)
  let c0 = mk_const("c_cons_guard", bool)
  let th_old = expect_ok_logic(logic_refl(st1, p0))
  let th_new = expect_ok_logic(logic_refl(st1, c0))
  assert_true(logic_conservative_replay_ok(st0, st1, th_old))
  assert_false(logic_conservative_replay_ok(st0, st1, th_new))
}
