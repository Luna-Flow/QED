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
  let key = DbConst("c", a)
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
