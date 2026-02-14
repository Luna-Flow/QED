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
