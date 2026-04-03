///|
using @kernel {
  db_term_eq,
  dest_fun_ty,
  bool_ty,
  empty_kernel_state,
  fun_ty,
  ind_ty,
  ks_add_const,
  ks_push_scope,
  mk_comb,
  mk_const,
  mk_tyvar,
  mk_var,
  ty_eq,
  type_of,
}

///|
fn[T, E] expect_ok_elab(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "elab var builder constructs variables" {
  let a = mk_tyvar("A")
  let x = elab_var("x", a)
  assert_true(x is Var("x", _))
}

///|
test "elab const wrappers use kernel lookup and schema checks" {
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_elab(ks_add_const(st0, "id", fun_ty(a, a)))

  assert_true(elab_const(st1, "id") is Ok(_))
  assert_true(elab_const(st1, "missing") is Err(UnknownConst))
  assert_true(elab_const_instance(st1, "id", fun_ty(bool, bool)) is Ok(_))
  assert_true(
    elab_const_instance(st1, "id", fun_ty(bool, a)) is Err(InvalidConstInstance),
  )
}

///|
test "elab app and app2 enforce post-construction typing" {
  let bool = bool_ty()
  let a = mk_tyvar("A")

  let f = mk_const("f", fun_ty(bool, bool))
  let x = mk_var("x", bool)
  let bad_x = mk_var("x_bad", a)
  assert_true(elab_app(f, x) is Ok(_))
  assert_true(elab_app(f, bad_x) is Err(TypeMismatch))

  let g = mk_const("g", fun_ty(bool, fun_ty(bool, bool)))
  let y = mk_var("y", bool)
  let bad_y = mk_var("y_bad", a)
  assert_true(elab_app2(g, x, y) is Ok(_))
  assert_true(elab_app2(g, x, bad_y) is Err(TypeMismatch))
}

///|
test "elab abs checks resulting term typing" {
  let bool = bool_ty()
  let x = mk_var("x", bool)
  assert_true(elab_abs("x", bool, x) is Ok(_))

  let bad_body = mk_comb(mk_const("c_bad", bool), x)
  assert_true(elab_abs("x", bool, bad_body) is Err(TypeMismatch))
}

///|
test "elab eq and proposition checks cover bool and non-bool terms" {
  let bool = bool_ty()
  let a = mk_tyvar("A")

  let p = mk_var("p", bool)
  let eq_pp = expect_ok_elab(elab_eq(p, p))
  assert_true(elab_is_prop(eq_pp))
  assert_true(elab_require_prop(eq_pp) is Ok(_))

  let x = mk_var("x", a)
  assert_false(elab_is_prop(x))
  assert_true(elab_require_prop(x) is Err(NotBoolTerm))

  let ill_typed = mk_comb(mk_const("c_ill", bool), p)
  assert_false(elab_is_prop(ill_typed))
  assert_true(elab_require_prop(ill_typed) is Err(TypeMismatch))

  let q = mk_var("q", a)
  assert_true(elab_eq(p, q) is Err(TypeMismatch))
}

///|
test "resolved constants freeze const ids across shadowing" {
  let bool = bool_ty()
  let st0 = expect_ok_elab(ks_add_const(empty_kernel_state(), "P", bool))
  let rt0 = match elab_resolve_const_by_name(st0, "P") {
    Ok(v) => v
    Err(_) => panic()
  }
  let st1 = ks_push_scope(st0)
  let st2 = expect_ok_elab(ks_add_const(st1, "P", fun_ty(bool, bool)))
  let rt1 = match elab_resolve_const_by_name(st2, "P") {
    Ok(v) => v
    Err(_) => panic()
  }

  assert_false(rconst_id(rt0) == rconst_id(rt1))
  assert_true(ty_eq(rconst_inst_ty(rt0), bool))
  assert_true(ty_eq(rconst_inst_ty(rt1), fun_ty(bool, bool)))

  let term0 = expect_ok_elab(elab_lower_to_term(rterm_const(rt0)))
  match type_of(term0) {
    Some(ty) => assert_true(ty_eq(ty, bool))
    None => panic()
  }
}

///|
test "resolved terms support polymorphic constant instances and core typing" {
  let a = mk_tyvar("A")
  let bool = bool_ty()
  let ind = ind_ty()
  let st0 = empty_kernel_state()
  let st1 = expect_ok_elab(ks_add_const(st0, "id", fun_ty(a, a)))
  let id_bool = match
    elab_resolve_const_instance(st1, "id", fun_ty(bool, bool)) {
    Ok(v) => v
    Err(_) => panic()
  }
  let id_ind = match elab_resolve_const_instance(st1, "id", fun_ty(ind, ind)) {
    Ok(v) => v
    Err(_) => panic()
  }
  let ctx = empty_elab_ctx()

  assert_true(elab_check_core_type(st1, ctx, id_bool, fun_ty(bool, bool)))
  assert_true(elab_check_core_type(st1, ctx, id_ind, fun_ty(ind, ind)))
}

///|
test "resolved abstraction lowers to debruijn consistently" {
  let bool = bool_ty()
  let ctx = empty_elab_ctx()
  let st = empty_kernel_state()
  let body = elab_resolve_var("x", bool)
  let rt = match elab_resolve_abs(st, ctx, "x", bool, body) {
    Ok(v) => v
    Err(_) => panic()
  }
  let term = expect_ok_elab(elab_lower_to_term(rt))
  let db1 = expect_ok_elab(elab_lower_to_db(rt))
  let db2 = match @kernel.to_db_term(term) {
    Some(v) => v
    None => panic()
  }
  assert_true(db_term_eq(db1, db2))
  match type_of(term) {
    Some(ty) =>
      match dest_fun_ty(ty) {
        Some((dom, cod)) => {
          assert_true(ty_eq(dom, bool))
          assert_true(ty_eq(cod, bool))
        }
        None => panic()
      }
    None => panic()
  }
}

///|
test "resolved free variable needs ctx for core typing" {
  let bool = bool_ty()
  let st = empty_kernel_state()
  let rt = elab_resolve_var("x", bool)
  assert_true(elab_core_type_of(st, empty_elab_ctx(), rt) is None)
  let ctx = elab_ctx_extend(empty_elab_ctx(), "x", bool)
  assert_true(elab_core_type_of(st, ctx, rt) is Some(_))
}

///|
test "elab_resolve_named_term rejects free variables outside ctx" {
  let bool = bool_ty()
  let st = empty_kernel_state()
  let x = mk_var("x", bool)
  assert_true(
    elab_resolve_named_term(st, empty_elab_ctx(), x) is Err(UnknownName(_)),
  )
  let ctx = elab_ctx_extend(empty_elab_ctx(), "x", bool)
  assert_true(elab_resolve_named_term(st, ctx, x) is Ok(_))
}
