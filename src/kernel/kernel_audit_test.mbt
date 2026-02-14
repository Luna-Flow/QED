///|
fn[T, E] expect_ok_audit(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn[T] expect_ok_sig_audit(res : Result[T, SigError]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn typedef_bundle_for_audit(ty : HolType) -> (Term, Thm) {
  let x = mk_var("x_td_audit", ty)
  let pred_body = expect_ok_audit(mk_eq(x, x))
  let pred = mk_abs(x, pred_body)
  let witness = expect_ok_audit(refl_checked(empty_kernel_state(), x))
  (pred, witness)
}

///|
test "audit c5 pop then redefine stays rejected by defheads" {
  let st0 = expect_ok_sig_audit(
    ks_add_const(empty_kernel_state(), "P", bool_ty()),
  )
  let p = mk_const("P", bool_ty())
  let (st1, _) = expect_ok_sig_audit(ks_define_const(st0, "q", bool_ty(), p))
  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig_audit(ks_pop_scope(st2))
  assert_true(
    ks_define_const(st3, "q", bool_ty(), p) is Err(DefinitionAlreadyExists),
  )
}

///|
test "audit c6 defhead cannot be shadowed as local constant" {
  let st0 = expect_ok_sig_audit(
    ks_add_const(empty_kernel_state(), "P", bool_ty()),
  )
  let p = mk_const("P", bool_ty())
  let (st1, _) = expect_ok_sig_audit(ks_define_const(st0, "q", bool_ty(), p))
  let st2 = ks_push_scope(st1)
  assert_true(ks_add_const(st2, "q", bool_ty()) is Err(DefinitionAlreadyExists))
}

///|
test "audit c7 deferred def-head cycle is rejected" {
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_sig_audit(ks_add_const(st1, "b", bool))
  let (st3, _) = expect_ok_sig_audit(
    ks_define_const(st2, "a", bool, mk_const("b", bool)),
  )
  let st4 = ks_push_scope(st3)
  assert_true(
    ks_define_const(st4, "b", bool, mk_const("a", bool))
    is Err(DefinitionIsCyclic),
  )
}

///|
test "audit d1 typedef rejects non theorem witness" {
  let st0 = empty_kernel_state()
  let x = mk_var("x", bool_ty())
  let pred_body = expect_ok_audit(mk_eq(x, x))
  let pred = mk_abs(x, pred_body)
  let bad_w = expect_ok_audit(assume_checked(st0, pred_body))
  assert_true(
    ks_register_type_definition(st0, "newty", ["A"], "RepAuditD1", pred, bad_w)
    is Err(InvalidTypeWitness),
  )
}

///|
test "audit d5 polymorphic constant instantiation guard" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st1 = expect_ok_sig_audit(ks_add_const(st0, "id", fun_ty(a, a)))
  let th = expect_ok_audit(refl_checked(st1, mk_const("id", fun_ty(a, a))))
  assert_true(inst_type(st1, [("A", bool)], th) is Ok(_))

  let st2 = ks_push_scope(st1)
  let st3 = expect_ok_sig_audit(ks_add_const(st2, "id", fun_ty(a, a)))
  let drifted = expect_ok_audit(refl_checked(st3, mk_const("id", fun_ty(a, a))))
  assert_true(inst_type(st1, [], drifted) is Err(InvalidInstantiation))
}

///|
test "audit d6 typedef witness const-id drift is rejected" {
  let bool = bool_ty()
  let st0 = expect_ok_sig_audit(ks_add_const(empty_kernel_state(), "W", bool))
  let w = mk_const("W", bool)
  let z = mk_var("z", bool)
  let pred = mk_abs(z, expect_ok_audit(mk_eq(w, w)))
  let witness = expect_ok_audit(refl_checked(st0, w))
  assert_true(
    ks_register_type_definition(st0, "tw0", [], "RepTW0", pred, witness)
    is Ok(_),
  )
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_sig_audit(ks_add_const(st1, "W", bool))
  assert_true(
    ks_register_type_definition(st2, "tw1", [], "RepTW1", pred, witness)
    is Err(InvalidTypeWitness),
  )
}

///|
test "audit e2 trans rejects typed middle mismatch" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let k = mk_var("k", fun_ty(a, a))
  let id_ok = mk_abs(x, x)
  let id_bad = mk_abs(x, y)

  let th1 = expect_ok_audit(
    assume_checked(st, expect_ok_audit(mk_eq(k, id_ok))),
  )
  let th2 = expect_ok_audit(
    assume_checked(st, expect_ok_audit(mk_eq(id_bad, k))),
  )
  assert_true(trans_checked(st, th1, th2) is Err(AlphaMismatch))
}

///|
test "audit e3 beta binder agreement check" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let y = mk_var("y", b)
  let redex = mk_comb(mk_abs(x, x), y)
  assert_true(beta_rule_checked(st, redex) is Err(TypeMismatch))
}

///|
test "audit conservativity replay for old-language sentence" {
  let bool = bool_ty()
  let st0 = expect_ok_sig_audit(ks_add_const(empty_kernel_state(), "P", bool))
  let p = mk_const("P", bool)
  let (st1, _) = expect_ok_sig_audit(ks_define_const(st0, "d_old", bool, p))

  let (td_pred, td_witness) = typedef_bundle_for_audit(bool)
  let st2 = expect_ok_sig_audit(
    ks_register_type_definition(
      st1,
      "auditty",
      [],
      "RepAuditTy",
      td_pred,
      td_witness,
    ),
  )

  let x = mk_var("x_spec_audit", bool)
  let spec_pred = mk_abs(x, expect_ok_audit(mk_eq(x, x)))
  let spec_witness = expect_ok_audit(refl_checked(st2, x))
  let (st3, _) = expect_ok_sig_audit(
    ks_specify_const(st2, "c_audit", bool, spec_pred, spec_witness),
  )

  let th_old = expect_ok_audit(refl_checked(st3, p))
  assert_true(ks_thm_is_sentence_in_language(st0, th_old))
  assert_true(ks_conservative_replay_ok(st0, st3, th_old))
}

///|
test "audit conservativity replay rejects non-old or non-sentence theorems" {
  let bool = bool_ty()
  let st0 = expect_ok_sig_audit(ks_add_const(empty_kernel_state(), "P", bool))
  let p = mk_const("P", bool)

  let x = mk_var("x_spec_audit2", bool)
  let spec_pred = mk_abs(x, expect_ok_audit(mk_eq(x, x)))
  let spec_witness = expect_ok_audit(refl_checked(st0, x))
  let (st1, _) = expect_ok_sig_audit(
    ks_specify_const(st0, "c_new", bool, spec_pred, spec_witness),
  )

  let c_new = mk_const("c_new", bool)
  let th_new = expect_ok_audit(refl_checked(st1, c_new))
  assert_false(ks_thm_is_sentence_in_language(st0, th_new))
  assert_false(ks_conservative_replay_ok(st0, st1, th_new))

  let th_hyp = expect_ok_audit(assume_checked(st1, p))
  assert_false(ks_thm_is_sentence_in_language(st0, th_hyp))
  assert_false(ks_conservative_replay_ok(st0, st1, th_hyp))
}
