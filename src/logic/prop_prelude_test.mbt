///|
using @kernel {ks_lookup_const}

///|
fn[T, E] expect_ok_prelude(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "install_prop_prelude is idempotent and registers logical constants" {
  let st0 = empty_kernel_state()
  let st1 = expect_ok_prelude(install_prop_prelude(st0))
  let st2 = expect_ok_prelude(install_prop_prelude(st1))

  assert_true(ks_lookup_const(st2, "imp") is Some(_))
  assert_true(ks_lookup_const(st2, "not") is Some(_))
  assert_true(ks_lookup_const(st2, "and") is Some(_))
  assert_true(ks_lookup_const(st2, "or") is Some(_))
}

///|
test "prop prelude constructors and destructors roundtrip by head symbol" {
  let prelude = default_prop_prelude()
  let st = expect_ok_prelude(install_prop_prelude(empty_kernel_state()))
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())

  let imp_pq = expect_ok_prelude(prop_mk_imp(st, prelude, p, q))
  let and_pq = expect_ok_prelude(prop_mk_and(st, prelude, p, q))
  let or_pq = expect_ok_prelude(prop_mk_or(st, prelude, p, q))
  let not_p = expect_ok_prelude(prop_mk_not(st, prelude, p))

  assert_true(prop_dest_imp(prelude, imp_pq) is Some((_, _)))
  assert_true(prop_dest_and(prelude, and_pq) is Some((_, _)))
  assert_true(prop_dest_or(prelude, or_pq) is Some((_, _)))
  assert_true(prop_dest_not(prelude, not_p) is Some(_))
}
