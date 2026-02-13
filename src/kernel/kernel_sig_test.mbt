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
test "kernel sig define_const rejects conflicting duplicate type" {
  let sig0 = empty_sig()
  let p = mk_const("P", bool_ty())
  let out1 = sig_define_const(sig0, "Q", p)
  assert_true(out1 is Some(_))
  match out1 {
    Some((sig1, _)) => {
      let x = mk_var("x", mk_tyvar("A"))
      let out2 = sig_define_const(sig1, "Q", x)
      assert_true(out2 is None)
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig define_const is replayable with same rhs type" {
  let sig0 = empty_sig()
  let p = mk_const("P", bool_ty())
  let out1 = sig_define_const(sig0, "Q", p)
  assert_true(out1 is Some(_))
  match out1 {
    Some((sig1, _)) => {
      let out2 = sig_define_const(sig1, "Q", p)
      assert_true(out2 is Some(_))
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig idempotent add accepts same type" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let s1 = sig_add_const_idempotent(sig0, "C", a)
  assert_true(s1 is Some(_))
  match s1 {
    Some(sig1) => {
      let s2 = sig_add_const_idempotent(sig1, "C", a)
      assert_true(s2 is Some(_))
      match s2 {
        Some(sig2) =>
          assert_true(sig_lookup_const(sig2, "C") is Some(TyVal("A")))
        None => assert_false(true)
      }
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig idempotent add rejects conflicting type" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let s1 = sig_add_const_idempotent(sig0, "C", a)
  assert_true(s1 is Some(_))
  match s1 {
    Some(sig1) => assert_true(sig_add_const_idempotent(sig1, "C", b) is None)
    None => assert_false(true)
  }
}

///|
test "kernel sig result api returns typed errors" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let s1 = sig_add_const_idempotent_e(sig0, "C", a)
  assert_true(s1 is Ok(_))
  match s1 {
    Ok(sig1) => {
      assert_true(sig_mk_const_e(sig1, "D") is Err(UnknownConst))
      assert_true(
        sig_add_const_idempotent_e(sig1, "C", b) is Err(ConstTypeConflict),
      )
      let p = mk_const("P", bool_ty())
      assert_true(sig_define_const_e(sig1, "Q", p) is Ok(_))
    }
    Err(_) => assert_false(true)
  }
}

///|
test "kernel sig supports shadowing across scopes" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let s1 = sig_add_const(sig0, "C", a)
  assert_true(s1 is Some(_))
  match s1 {
    Some(sig1) => {
      let sig2 = sig_push_scope(sig1)
      let s3 = sig_add_const(sig2, "C", b)
      assert_true(s3 is Some(_))
      match s3 {
        Some(sig3) =>
          assert_true(sig_lookup_const(sig3, "C") is Some(TyVal("B")))
        None => assert_false(true)
      }
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig pop_scope restores outer binding" {
  let sig0 = empty_sig()
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let s1 = sig_add_const(sig0, "C", a)
  assert_true(s1 is Some(_))
  match s1 {
    Some(sig1) => {
      let sig2 = sig_push_scope(sig1)
      let s3 = sig_add_const(sig2, "C", b)
      assert_true(s3 is Some(_))
      match s3 {
        Some(sig3) =>
          match sig_pop_scope(sig3) {
            Some(sig4) =>
              assert_true(sig_lookup_const(sig4, "C") is Some(TyVal("A")))
            None => assert_false(true)
          }
        None => assert_false(true)
      }
    }
    None => assert_false(true)
  }
}

///|
test "kernel sig pop_scope rejects root underflow" {
  assert_true(sig_pop_scope(empty_sig()) is None)
  assert_true(sig_pop_scope_e(empty_sig()) is Err(ScopeUnderflow))
}
