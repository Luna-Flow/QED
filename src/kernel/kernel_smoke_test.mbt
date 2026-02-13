///|
test "kernel phase0 smoke" {
  assert_true(bool_ty() is TyApp("bool", _))
  assert_eq(kernel_terms_phase0_ready(), true)
  assert_eq(kernel_thm_phase0_ready(), true)
}
