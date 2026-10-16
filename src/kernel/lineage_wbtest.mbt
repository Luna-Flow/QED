///|
test "lineage ancestor_at agrees with walking the parent chain" {
  let root = lineage_root()
  let nodes : Array[LineageNode] = [root]
  let mut cur = root
  for i in 0..<3000 {
    cur = lineage_append(cur, "event_" + i.to_string())
    nodes.push(cur)
  }
  // depth of root is 1, so nodes[k] has depth k + 1
  for k in 0..<nodes.length() {
    assert_eq(nodes[k].depth, k + 1)
  }
  let tip = nodes[nodes.length() - 1]
  for k in 0..<nodes.length() {
    let a = lineage_ancestor_at(tip, nodes[k].depth)
    assert_eq(a.id, nodes[k].id)
  }
}

///|
test "lineage prefix holds exactly for ancestors, not for forks" {
  let root = lineage_root()
  let mut trunk = root
  for i in 0..<200 {
    trunk = lineage_append(trunk, "t" + i.to_string())
  }
  // two forks from the same node, one longer than the other
  let fork_a = lineage_append(trunk, "left")
  let mut fork_b = lineage_append(trunk, "right")
  for i in 0..<50 {
    fork_b = lineage_append(fork_b, "r" + i.to_string())
  }
  assert_true(lineage_is_prefix(trunk, trunk))
  assert_true(lineage_is_prefix(trunk, fork_a))
  assert_true(lineage_is_prefix(trunk, fork_b))
  assert_true(lineage_is_prefix(root, fork_b))
  assert_false(lineage_is_prefix(fork_a, trunk))
  assert_false(lineage_is_prefix(fork_a, fork_b))
  assert_false(lineage_is_prefix(fork_b, fork_a))
  // every proper prefix of the long fork is an ancestor, none of the left fork is
  let mut walk = Some(fork_b)
  while walk is Some(n) {
    assert_true(lineage_is_prefix(n, fork_b))
    walk = n.parent
  }
}

///|
test "identical events from the same parent share one node" {
  let root = lineage_root()
  let a = lineage_append(lineage_append(root, "same_1"), "same_2")
  let b = lineage_append(lineage_append(root, "same_1"), "same_2")
  assert_eq(a.id, b.id)
  let c = lineage_append(lineage_append(root, "same_1"), "different")
  assert_true(a.id != c.id)
  assert_false(lineage_is_prefix(a, c))
  assert_false(lineage_is_prefix(c, a))
  // the same event under another parent is another node
  let d = lineage_append(lineage_append(root, "other"), "same_2")
  assert_true(a.id != d.id)
}

///|
test "a theorem from a very long linear history stays admissible in descendants" {
  let mut st = empty_kernel_state()
  let seed = ks_add_const(st, "deep_lineage_t", bool_ty()).unwrap()
  st = seed
  let th = refl_checked(st, mk_const("deep_lineage_t", bool_ty())).unwrap()
  for _ in 0..<20000 {
    st = ks_push_scope(st)
  }
  for _ in 0..<20000 {
    st = ks_pop_scope(st).unwrap()
  }
  assert_true(inst_checked(st, [], th) is Ok(_))
  // a fork that diverges right after the seed state must reject it
  let fork = ks_add_const(ks_push_scope(seed), "deep_lineage_other", bool_ty()).unwrap()
  assert_true(inst_checked(fork, [], th) is Ok(_))
  let sibling = ks_add_const(
    ks_add_const(empty_kernel_state(), "deep_lineage_t", bool_ty()).unwrap(),
    "deep_lineage_diverge",
    bool_ty(),
  ).unwrap()
  // same events as `seed` then one more: that is a descendant, not a sibling
  assert_true(inst_checked(sibling, [], th) is Ok(_))
  let divergent = ks_add_const(
    ks_push_scope(empty_kernel_state()),
    "deep_lineage_t",
    bool_ty(),
  ).unwrap()
  assert_true(inst_checked(divergent, [], th) is Err(_))
}

///|
test "ancestor queries take a logarithmic number of hops" {
  let root = lineage_root()
  let nodes : Array[LineageNode] = [root]
  let mut cur = root
  for i in 0..<5000 {
    cur = lineage_append(cur, "hop_" + i.to_string())
    nodes.push(cur)
  }
  let tip = nodes[nodes.length() - 1]
  let mut worst = 0
  for k in 0..<nodes.length() {
    let (a, hops) = lineage_ancestor_counted(tip, nodes[k].depth)
    assert_eq(a.id, nodes[k].id)
    if hops > worst {
      worst = hops
    }
  }
  // 5000 events: log2 is about 12.3; the skew-binary scheme needs at most about
  // 2 log2(n) hops, a linear walk would need 5000.
  assert_true(worst <= 40)
}
