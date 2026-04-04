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
  let prelude = default_prop_prelude()

  assert_true(ks_lookup_const(st2, prop_truth_name(prelude)) is Some(_))
  assert_true(ks_lookup_const(st2, prop_false_name(prelude)) is Some(_))
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

  assert_true(prop_dest_imp(st, prelude, imp_pq) is Some((_, _)))
  assert_true(prop_dest_and(st, prelude, and_pq) is Some((_, _)))
  assert_true(prop_dest_or(st, prelude, or_pq) is Some((_, _)))
  assert_true(prop_dest_not(st, prelude, not_p) is Some(_))
}

///|
test "prop prelude builders reject non-bool inputs without panicking" {
  let prelude = default_prop_prelude()
  let st = empty_kernel_state()
  let x = mk_var("x", mk_tyvar("A"))
  let y = mk_var("y", mk_tyvar("A"))

  assert_true(
    match prop_mk_not(st, prelude, x) {
      Err(NotBoolTerm) => true
      _ => false
    },
  )
  assert_true(
    match prop_mk_imp(st, prelude, x, y) {
      Err(NotBoolTerm) => true
      _ => false
    },
  )
  assert_true(
    match prop_mk_and(st, prelude, x, y) {
      Err(NotBoolTerm) => true
      _ => false
    },
  )
  assert_true(
    match prop_mk_or(st, prelude, x, y) {
      Err(NotBoolTerm) => true
      _ => false
    },
  )
}

///|
test "install_prop_prelude rejects same-typed noncanonical connector collision" {
  let bool = bool_ty()
  let bin = fun_ty(bool, fun_ty(bool, bool))
  let st0 = expect_ok_prelude(ks_add_const(empty_kernel_state(), "imp", bin))
  assert_true(install_prop_prelude(st0) is Err(DefinitionAlreadyExists))
}

///|
test "prop foundation exposes definition theorems for prelude connectors" {
  let prelude = default_prop_prelude()
  let st = expect_ok_prelude(install_prop_prelude(empty_kernel_state()))

  let th_imp = expect_ok_prelude(logic_prop_def_imp(st, prelude))
  let th_and = expect_ok_prelude(logic_prop_def_and(st, prelude))
  let th_or = expect_ok_prelude(logic_prop_def_or(st, prelude))
  let th_not = expect_ok_prelude(logic_prop_def_not(st, prelude))

  assert_eq(thm_hyp_count(th_imp), 0)
  assert_eq(thm_hyp_count(th_and), 0)
  assert_eq(thm_hyp_count(th_or), 0)
  assert_eq(thm_hyp_count(th_not), 0)

  assert_true(thm_concl(th_imp) is Ok(_))
  assert_true(thm_concl(th_and) is Ok(_))
  assert_true(thm_concl(th_or) is Ok(_))
  assert_true(thm_concl(th_not) is Ok(_))
}

///|
test "prop foundation exposes stable definition theorem shape for implication" {
  let prelude = default_prop_prelude()
  let st = expect_ok_prelude(install_prop_prelude(empty_kernel_state()))
  let imp_c = expect_ok_prelude(ks_mk_const(st, prelude.imp_name))
  let def_th = expect_ok_prelude(logic_prop_def_imp(st, prelude))
  let lhs = expect_ok_prelude(logic_prop_def_lhs(def_th))
  let rhs = expect_ok_prelude(logic_prop_def_rhs(def_th))
  assert_true(term_alpha_eq(lhs, imp_c))
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())
  let expected = expect_ok_prelude(prop_mk_imp(st, prelude, p, q))
  assert_true(type_of(rhs) is Some(_))
  assert_true(type_of(expected) is Some(_))
  match thm_concl(def_th) {
    Ok(_) => ()
    Err(_) => panic()
  }
}
