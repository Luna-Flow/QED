///|
fn[T, E] expect_ok_logic(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn typedef_bundle_logic(
  ty : @kernel.HolType,
  name : String,
) -> (@kernel.Term, @kernel.Thm) {
  let x = @kernel.mk_var(name, ty)
  let body = expect_ok_logic(@kernel.mk_eq(x, x))
  let pred = @kernel.mk_abs(x, body)
  let witness = expect_ok_logic(logic_refl(@kernel.empty_kernel_state(), x))
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
  let spec_witness = expect_ok_logic(logic_refl(st1, x))
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
