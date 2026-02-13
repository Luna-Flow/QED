///|
test "kernel sig add and lookup constant" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let sig1 = sig_add_const(sig0, "C", a)
  assert_true(sig1 is Some(_))
  match sig1 {
    Some(sig) => {
      assert_true(sig_has_const(sig, "C"))
      assert_true(sig_lookup_const(sig, "C") is Some(TyVal("A")))
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig rejects duplicate constant names" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let sig1 = sig_add_const(sig0, "C", a)
  assert_true(sig1 is Some(_))
  match sig1 {
    Some(sig) => {
      let out = sig_add_const(sig, "C", b)
      assert_true(out is None)
    }
    None => assert_false(true)
  }
}
