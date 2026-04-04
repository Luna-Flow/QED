///|
fn[T, E] expect_ok_tools(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "prop tools truth theorem is closed and boolean" {
  let st = empty_kernel_state()
  let th = expect_ok_tools(logic_prop_truth_thm(st))
  assert_eq(thm_hyp_count(th), 0)
  match thm_concl(th) {
    Ok(concl) => assert_true(type_of(concl) is Some(_))
    Err(_) => panic()
  }
}

///|
test "prop tools truth const theorem after prelude" {
  let prelude = default_prop_prelude()
  let st = expect_ok_tools(install_prop_prelude(empty_kernel_state()))
  let th = expect_ok_tools(logic_prop_truth_const_thm(st, prelude))
  assert_eq(thm_hyp_count(th), 0)
}

///|
test "prop tools apply function equality lifts over one and two arguments" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let c = mk_tyvar("C")
  let f = mk_var("f", fun_ty(a, b))
  let g = mk_var("g", fun_ty(a, b))
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let h = mk_var("h", fun_ty(a, fun_ty(b, c)))
  let k = mk_var("k", fun_ty(a, fun_ty(b, c)))
  let z = mk_var("z", b)

  let th_fg = expect_ok_tools(logic_assume(st, expect_ok_tools(mk_eq(f, g))))
  let th_hk = expect_ok_tools(logic_assume(st, expect_ok_tools(mk_eq(h, k))))

  let th_fxgx = expect_ok_tools(logic_apply_fun_eq(st, th_fg, x))
  let th_hxkxz = expect_ok_tools(logic_apply_fun_eq2(st, th_hk, y, z))

  assert_true(thm_concl(th_fxgx) is Ok(_))
  assert_true(thm_concl(th_hxkxz) is Ok(_))
}

///|
test "prop tools beta normalize and eq symmetry work" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let redex = mk_comb(mk_abs(x, x), y)
  let th_redex = expect_ok_tools(logic_refl(st, redex))
  let th_norm = expect_ok_tools(logic_beta_normalize_eq(st, th_redex))
  assert_true(thm_concl(th_norm) is Ok(_))

  let th_xy = expect_ok_tools(logic_assume(st, expect_ok_tools(mk_eq(x, y))))
  let th_yx = expect_ok_tools(logic_eq_sym(st, th_xy))
  match thm_concl(th_yx) {
    Ok(concl) =>
      match dest_eq(concl) {
        Ok((lhs, rhs)) => {
          assert_true(term_alpha_eq(lhs, y))
          assert_true(term_alpha_eq(rhs, x))
        }
        Err(_) => panic()
      }
    Err(_) => panic()
  }
}

///|
test "prop tools eq_mp_bool rejects non-bool theorem" {
  let st = empty_kernel_state()
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let p = mk_var("p", bool_ty())
  let q = mk_var("q", bool_ty())

  let th_eq = expect_ok_tools(logic_assume(st, expect_ok_tools(mk_eq(p, q))))
  let th_non_bool = expect_ok_tools(logic_refl(st, x))
  assert_true(logic_eq_mp_bool(st, th_eq, th_non_bool) is Err(_))
  let th_p = expect_ok_tools(logic_assume(st, p))
  assert_true(logic_eq_mp_bool(st, th_eq, th_p) is Ok(_))
}
