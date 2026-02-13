///|
test "kernel phase0 smoke" {
  assert_eq(kernel_types_phase0_ready(), true)
  assert_eq(kernel_terms_phase0_ready(), true)
  assert_eq(kernel_thm_phase0_ready(), true)
}
