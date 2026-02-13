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

///|
test "kernel sig mk_const only for registered names" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let sig1 = sig_add_const(sig0, "C", a)
  assert_true(sig1 is Some(_))
  match sig1 {
    Some(sig) => {
      let c = sig_mk_const(sig, "C")
      let d = sig_mk_const(sig, "D")
      assert_true(c is Some(Const("C", _)))
      assert_true(d is None)
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig define_const creates definitional equation term" {
  let sig0 = empty_sig()
  let p = mk_const("P", bool_ty())
  let out = sig_define_const(sig0, "Q", p)
  assert_true(out is Some(_))
  match out {
    Some((sig1, def_eq)) => {
      assert_true(sig_has_const(sig1, "Q"))
      assert_true(
        def_eq is Comb(Comb(Const("=", _), Const("Q", _)), Const("P", _)),
      )
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig define_const rejects duplicate names" {
  let sig0 = empty_sig()
  let p = mk_const("P", bool_ty())
  let out1 = sig_define_const(sig0, "Q", p)
  assert_true(out1 is Some(_))
  match out1 {
    Some((sig1, _)) => {
      let out2 = sig_define_const(sig1, "Q", p)
      assert_true(out2 is None)
    }
    None => assert_false(true)
  }
}
