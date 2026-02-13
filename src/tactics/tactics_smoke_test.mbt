///|
test "tactics phase0 smoke" {
  assert_eq(tactics_goal_phase0_ready(), true)
  assert_eq(tactics_engine_phase0_ready(), true)
}
