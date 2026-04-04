///|
test "wb inst substitution rejects captured bound image" {
  let a = mk_tyvar("A")
  let key = DbFree("x", a)
  let value = DbBound(0, a)
  assert_true(validate_db_inst_subst([(key, value)]) is Err(VariableCaptured))
}

///|
test "wb inst substitution rejects non-free keys" {
  let a = mk_tyvar("A")
  let key = DbConst("c", a, -1)
  let value = DbFree("x", a)
  assert_true(
    validate_db_inst_subst([(key, value)]) is Err(InvalidInstantiation),
  )
}

///|
test "wb db_beta_reduce_once fails closed on debruijn index overflow" {
  let ty = bool_ty()
  let max = 2147483647
  let redex = DbComb(DbAbs(ty, DbBound(0, ty)), DbBound(max, ty))
  assert_true(db_beta_reduce_once(redex) is None)
}

///|
test "wb db_subst_free_parallel fails closed on shift overflow" {
  let ty = bool_ty()
  let max = 2147483647
  let term = DbAbs(ty, DbFree("x_cap", ty))
  let key = DbFree("x_cap", ty)
  let repl = DbBound(max, ty)
  assert_true(db_subst_free_parallel(term, [(key, repl)]) is None)
}

///|
fn[T, E] expect_ok_wb(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "wb ghost typed theorems fail admissibility and sentence checks" {
  let st = empty_kernel_state()
  let ghost = mk_tyapp("ghost", [])
  let x = mk_var("xg_wb", ghost)
  let idg = mk_abs(x, x)
  let eq = expect_ok_wb(mk_eq(idg, idg))
  let eq_db = match to_db_term(eq) {
    Some(v) => v
    None => panic()
  }
  let th = mk_thm([], eq_db)

  assert_true(ensure_thm_admissible(st, th) is Err(InvalidInstantiation))
  assert_false(thm_is_admissible(st, th))
  assert_false(ks_thm_is_sentence_in_language(st, th))
  assert_false(ks_conservative_replay_ok(st, st, th))
}
