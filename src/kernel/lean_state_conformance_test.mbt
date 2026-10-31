// Conformance tests for the Lean model of kernel states, theorem objects,
// lineage and name resolution (KernelState.lean, NameResolution.lean,
// DeclarationAllocation.lean).
//
// Lean models a state as a history with allocation bounds; `KStep.extend`
// appends a definition, specification or type definition, `KStep.alloc`
// allocates an opaque constant, and a theorem is admissible exactly in the
// states reachable from its origin. Each test is named after the Lean
// constructor or theorem it follows.

///|
fn[T, E] ls_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
/// `@ (λw. w = w)`, a closed term of any type.
fn ls_closed_term(ty : HolType) -> Term {
  let w = mk_var("w", ty)
  mk_comb(
    mk_const("@", fun_ty(fun_ty(ty, bool_ty()), ty)),
    mk_abs(w, ls_ok(mk_eq(w, w))),
  )
}

///|
fn ls_define(st : KernelState, name : String, rhs : Term) -> (KernelState, Thm) {
  ls_ok(ks_define_const_thm(st, name, type_of(rhs).unwrap(), rhs))
}

///|
fn ls_id(st : KernelState, name : String) -> Int32 {
  ks_lookup_const_id(st, name).unwrap()
}

///|
test "KStep.extend: an extension step keeps older theorems and adds new ones" {
  let st0 = empty_kernel_state()
  let old = ls_ok(refl_checked(st0, ls_closed_term(bool_ty())))
  let (st1, def_th) = ls_define(st0, "d", ls_closed_term(bool_ty()))
  assert_true(thm_is_admissible(st1, old))
  assert_true(thm_is_admissible(st1, def_th))
  // The new theorem's origin is the extended state, not the old one.
  assert_false(thm_is_admissible(st0, def_th))
}

///|
test "KStep.alloc: an opaque allocation keeps older theorems" {
  let st0 = empty_kernel_state()
  let old = ls_ok(refl_checked(st0, ls_closed_term(bool_ty())))
  let st1 = ls_ok(ks_add_const(st0, "k", bool_ty()))
  assert_true(thm_is_admissible(st1, old))
  let k = ls_ok(ks_mk_const(st1, "k"))
  let th = ls_ok(refl_checked(st1, k))
  assert_false(thm_is_admissible(st0, th))
}

///|
test "KStep.bounds: constant identities increase along every step" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let st1 = ls_ok(ks_add_const(st0, "k1", bool))
  let (st2, _) = ls_define(st1, "d1", ls_closed_term(bool))
  let st3 = ls_ok(
    ks_register_type_definition(
      st2,
      "u",
      [],
      "rep_u",
      mk_abs(
        mk_var("x", bool),
        ls_ok(mk_eq(mk_var("x", bool), mk_var("x", bool))),
      ),
      ls_ok(refl_checked(st2, ls_closed_term(bool))),
    ),
  )
  let st4 = ls_ok(ks_add_const(st3, "k2", bool))
  let ids = [
    ls_id(st4, "k1"),
    ls_id(st4, "d1"),
    ls_id(st4, "rep_u"),
    ls_id(st4, "Abs_u"),
    ls_id(st4, "k2"),
  ]
  for i in 1..<ids.length() {
    assert_true(ids[i - 1] < ids[i])
  }
}

///|
test "KState.WF.fresh: an identity is never allocated twice, even after a scope is popped" {
  let st0 = empty_kernel_state()
  let st1 = ls_ok(ks_add_const(ks_push_scope(st0), "c", bool_ty()))
  let first = ls_id(st1, "c")
  let st2 = ls_ok(ks_pop_scope(st1))
  assert_true(ks_lookup_const_id(st2, "c") is None)
  let st3 = ls_ok(ks_add_const(st2, "c", bool_ty()))
  assert_true(ls_id(st3, "c") != first)
}

///|
test "KReach.lift: a theorem is admissible in every state reachable from its origin" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let th = ls_ok(refl_checked(st0, ls_closed_term(a)))
  let mut st = st0
  for i in 0..<4 {
    st = ls_define(st, "d" + i.to_string(), ls_closed_term(bool_ty())).0
    st = ls_ok(ks_add_const(st, "k" + i.to_string(), bool_ty()))
    assert_true(thm_is_admissible(st, th))
  }
  // Pushing a scope does not change the history.
  assert_true(thm_is_admissible(ks_push_scope(st), th))
}

///|
test "LineageCode.admissible: a theorem of one branch is not admissible in a sibling" {
  let st0 = empty_kernel_state()
  let bool = bool_ty()
  let p = mk_var("p", bool)
  let (left, th_left) = ls_define(st0, "d", ls_closed_term(bool))
  let (right, th_right) = ls_define(
    st0,
    "d",
    ls_ok(mk_eq(mk_abs(p, p), mk_abs(p, p))),
  )
  assert_false(thm_is_admissible(right, th_left))
  assert_false(thm_is_admissible(left, th_right))
  // Neither can a theorem of the sibling be combined with one of this branch.
  let refl_right = ls_ok(refl_checked(right, ls_ok(ks_mk_const(right, "d"))))
  assert_true(trans_checked(right, th_left, refl_right) is Err(_))
  // Theorems made inside a popped scope do not survive the pop.
  let inner = ls_ok(ks_add_const(ks_push_scope(st0), "s", bool))
  let th_inner = ls_ok(refl_checked(inner, ls_ok(ks_mk_const(inner, "s"))))
  assert_false(thm_is_admissible(ls_ok(ks_pop_scope(inner)), th_inner))
}

///|
test "Term.eq_of_named_eq: a shadowed name no longer resolves to the old constant" {
  // Rules compare constants by name; this is sound because an admissible
  // theorem resolves every name it mentions to the identity it carries.
  let st1 = ls_ok(ks_add_const(empty_kernel_state(), "c", bool_ty()))
  let c_old = ls_ok(ks_mk_const(st1, "c"))
  let th_old = ls_ok(refl_checked(st1, c_old))
  let st2 = ls_ok(ks_add_const(ks_push_scope(st1), "c", bool_ty()))
  let c_new = ls_ok(ks_mk_const(st2, "c"))
  assert_true(ls_id(st1, "c") != ls_id(st2, "c"))
  assert_false(thm_is_admissible(st2, th_old))
  let th_new = ls_ok(refl_checked(st2, c_new))
  assert_true(trans_checked(st2, th_old, th_new) is Err(_))
  assert_true(trans_checked(st2, th_new, th_old) is Err(_))
}

///|
test "Sequent.mem_hyps_of_named: a hypothesis is not discharged by a shadowing constant" {
  let st1 = ls_ok(ks_add_const(empty_kernel_state(), "c", bool_ty()))
  let th_old = ls_ok(assume_checked(st1, ls_ok(ks_mk_const(st1, "c"))))
  let st2 = ls_ok(ks_add_const(ks_push_scope(st1), "c", bool_ty()))
  let th_new = ls_ok(assume_checked(st2, ls_ok(ks_mk_const(st2, "c"))))
  assert_true(deduct_antisym_rule_checked(st2, th_old, th_new) is Err(_))
  // Within one state the same name is the same hypothesis, so each
  // conclusion discharges the other hypothesis.
  let th_new2 = ls_ok(assume_checked(st2, ls_ok(ks_mk_const(st2, "c"))))
  let th = ls_ok(deduct_antisym_rule_checked(st2, th_new, th_new2))
  assert_eq(thm_hyp_count(th), 0)
}

///|
test "DeclTable.old_declares_after_add: older constants keep their identity and type" {
  let st0 = empty_kernel_state()
  let a = mk_tyvar("A")
  let st1 = ls_ok(ks_add_const(st0, "f", fun_ty(a, a)))
  let id = ls_id(st1, "f")
  let (st2, _) = ls_define(st1, "d", ls_closed_term(bool_ty()))
  let st3 = ls_ok(ks_add_const(st2, "g", bool_ty()))
  assert_eq(ls_id(st3, "f"), id)
  assert_true(ty_eq(ks_const_schema(st3, "f").unwrap(), fun_ty(a, a)))
}

///|
test "DeclTable.declared_type_unique: a name in one scope has one type" {
  let st1 = ls_ok(ks_add_const(empty_kernel_state(), "c", bool_ty()))
  assert_true(ks_add_const(st1, "c", ind_ty()) is Err(_))
  match ks_add_const(st1, "c", bool_ty()) {
    // Re-adding the same declaration may be accepted as a no-op.
    Ok(st2) => assert_eq(ls_id(st2, "c"), ls_id(st1, "c"))
    Err(_) => ()
  }
}
