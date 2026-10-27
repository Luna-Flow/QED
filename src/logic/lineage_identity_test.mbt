///|
/// Regression for #70: two sibling definitions whose right-hand sides print
/// identically (`x` stamped with its id versus the unstamped name `x#<id>`)
/// must not share a lineage node, otherwise a theorem from one sibling is
/// admissible in the other and `⊢ F` follows.
test "sibling definitions with colliding printouts get distinct lineage" {
  let bool = @kernel.bool_ty()
  let t = @logic.logic_prop_truth_term()
  let f = @logic.logic_prop_false_term()
  let st0 = @kernel.empty_kernel_state()
  let (st1, _) = @kernel.ks_define_const(st0, "x", bool, t).unwrap()
  let xid = @kernel.ks_lookup_const_id(st1, "x").unwrap()
  let shadow = "x#\{xid}"
  let (st2, _) = @kernel.ks_define_const(st1, shadow, bool, f).unwrap()
  let (sa, _) = @kernel.ks_define_const(
    st2,
    "d",
    bool,
    @kernel.mk_const_bound("x", bool, xid),
  ).unwrap()
  let (sb, _) = @kernel.ks_define_const(
    st2,
    "d",
    bool,
    @kernel.mk_const(shadow, bool),
  ).unwrap()
  let da = @kernel.ks_definition_theorem(sa, "d").unwrap()
  let db = @kernel.ks_definition_theorem(sb, "d").unwrap()
  assert_false(@kernel.thm_is_admissible(sb, da))
  assert_true(@kernel.thm_is_admissible(sb, db))
  let sym = @logic.logic_eq_sym(sb, da)
  match sym {
    Ok(da_sym) => assert_true(@kernel.trans_checked(sb, da_sym, db) is Err(_))
    Err(_) => ()
  }
}
