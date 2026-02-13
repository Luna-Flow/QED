///|
test "terms constructors" {
  let bool = bool_ty()

  let v = mk_var("x", bool)
  assert_true(v is Var("x", _))

  let c = mk_const("T", bool)
  assert_true(c is Const("T", _))
}

///|
test "terms type_of" {
  let a = mk_tyvar("A")

  let v = mk_var("x", a)
  assert_true(type_of(v) is TyVal("A"))

  let c = mk_const("k", bool_ty())
  assert_true(type_of(c) is TyApp("bool", []))
}

///|
test "terms comb constructor" {
  let bool = bool_ty()
  let f_ty = fun_ty(bool, bool)
  let f = mk_const("f", f_ty)
  let x = mk_var("x", bool)
  let app = mk_comb(f, x)
  assert_true(app is Comb(_, _))
}

///|
test "terms comb type_of" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let f = mk_const("f", fun_ty(a, b))
  let x = mk_var("x", a)
  let app = mk_comb(f, x)
  assert_true(type_of(app) is TyVal("B"))
}

///|
test "terms abs constructor" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let body = mk_var("y", a)
  let lam = mk_abs(x, body)
  assert_true(lam is Abs(_, _))
}

///|
test "terms abs type_of" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  let x = mk_var("x", a)
  let k = mk_const("k", b)
  let lam = mk_abs(x, k)
  assert_true(type_of(lam) is TyApp("fun", [TyVal("A"), TyVal("B")]))
}

///|
test "terms predicates" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, c)

  assert_true(is_var(x))
  assert_false(is_var(c))

  assert_true(is_const(c))
  assert_false(is_const(app))

  assert_true(is_comb(app))
  assert_false(is_comb(lam))

  assert_true(is_abs(lam))
  assert_false(is_abs(x))
}

///|
test "terms destructors" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, c)

  assert_true(dest_var(x) is Some(("x", _)))
  assert_true(dest_var(c) is None)

  assert_true(dest_const(c) is Some(("c", _)))
  assert_true(dest_const(x) is None)

  assert_true(dest_comb(app) is Some((_, _)))
  assert_true(dest_comb(lam) is None)

  assert_true(dest_abs(lam) is Some((_, _)))
  assert_true(dest_abs(app) is None)
}

///|
test "terms pretty printer" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let c = mk_const("c", a)
  let app = mk_comb(c, x)
  let lam = mk_abs(x, app)

  let rendered = term_to_string(lam)
  assert_true(rendered.contains("Abs("))
  assert_true(rendered.contains("Comb("))
  assert_true(rendered.contains("Var(x : A)"))
}

///|
test "terms debruijn string keeps alpha shape" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)

  let t1 = mk_abs(x, x)
  let t2 = mk_abs(y, y)

  assert_eq(db_string(t1), db_string(t2))
  assert_true(db_string(t1).contains("BVar(0 : A)"))
}

///|
test "terms to_db_term preserves alpha-invariant structure" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)

  let t1 = mk_abs(x, mk_comb(x, x))
  let t2 = mk_abs(y, mk_comb(y, y))

  let d1 = to_db_term(t1)
  let d2 = to_db_term(t2)
  assert_true((d1, d2) is (Some(_), Some(_)))

  match (d1, d2) {
    (Some(v1), Some(v2)) => {
      assert_eq(db_term_to_string(v1), db_term_to_string(v2))
      assert_true(db_term_to_string(v1).contains("BVar(0 : A)"))
    }
    _ => assert_false(true)
  }
}

///|
test "terms to_db_term rejects non-variable binder" {
  let a = mk_tyvar("A")
  let c = mk_const("c", a)
  let x = mk_var("x", a)
  let bad = mk_abs(c, x)
  assert_true(to_db_term(bad) is None)
}

///|
test "terms db_term_eq checks structural equality" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let t1 = mk_abs(x, mk_comb(x, y))
  let t2 = mk_abs(z, mk_comb(z, y))
  let t3 = mk_abs(z, mk_comb(y, z))

  let d1 = to_db_term(t1)
  let d2 = to_db_term(t2)
  let d3 = to_db_term(t3)
  assert_true((d1, d2, d3) is (Some(_), Some(_), Some(_)))

  match (d1, d2, d3) {
    (Some(v1), Some(v2), Some(v3)) => {
      assert_true(db_term_eq(v1, v2))
      assert_false(db_term_eq(v1, v3))
    }
    _ => assert_false(true)
  }
}

///|
test "terms db_beta_reduce_once reduces identity application" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let redex = mk_comb(mk_abs(x, x), y)

  let db_redex = to_db_term(redex)
  let db_y = to_db_term(y)
  assert_true((db_redex, db_y) is (Some(_), Some(_)))

  match (db_redex, db_y) {
    (Some(r), Some(y2)) =>
      match db_beta_reduce_once(r) {
        Some(out) => assert_true(db_term_eq(out, y2))
        None => assert_false(true)
      }
    _ => assert_false(true)
  }
}

///|
test "terms db_beta_reduce_once avoids capture by construction" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let body = mk_abs(y, x)
  let redex = mk_comb(mk_abs(x, body), y)

  let db_redex = to_db_term(redex)
  assert_true(db_redex is Some(_))
  match db_redex {
    Some(r) =>
      match db_beta_reduce_once(r) {
        Some(out) => assert_true(db_term_to_string(out).contains("FVar(y : A)"))
        None => assert_false(true)
      }
    None => assert_false(true)
  }
}

///|
test "terms from_db_term round-trips up to alpha equivalence" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let t = mk_abs(x, mk_comb(x, y))

  let db = to_db_term(t)
  assert_true(db is Some(_))
  match db {
    Some(dt) =>
      match from_db_term(dt) {
        Some(t2) =>
          match (to_db_term(t), to_db_term(t2)) {
            (Some(d1), Some(d2)) => assert_true(db_term_eq(d1, d2))
            _ => assert_false(true)
          }
        None => assert_false(true)
      }
    None => assert_false(true)
  }
}

///|
test "terms db_subst_free_parallel is capture-avoiding" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let term = mk_abs(y, x)

  let d_term = to_db_term(term)
  let d_repl = to_db_term(y)
  assert_true((d_term, d_repl) is (Some(_), Some(_)))
  match (d_term, d_repl) {
    (Some(tdb), Some(rdb)) => {
      let d_key = to_db_term(x)
      assert_true(d_key is Some(_))
      match d_key {
        Some(kdb) => {
          let out = db_subst_free_parallel(tdb, [(kdb, rdb)])
          assert_true(db_term_to_string(out).contains("FVar(y : A)"))
        }
        None => assert_false(true)
      }
    }
    _ => assert_false(true)
  }
}

///|
test "terms db_has_free_var detects free occurrence" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let t = mk_comb(x, y)
  let db = to_db_term(t)
  assert_true(db is Some(_))
  match db {
    Some(d) => {
      assert_true(db_has_free_var(d, "x", a))
      assert_false(db_has_free_var(d, "z", a))
    }
    None => assert_false(true)
  }
}

///|
test "terms db_has_free_var does not count bound occurrence" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let t = mk_abs(x, x)
  let db = to_db_term(t)
  assert_true(db is Some(_))
  match db {
    Some(d) => assert_false(db_has_free_var(d, "x", a))
    None => assert_false(true)
  }
}

///|
test "terms term_alpha_eq uses debruijn semantics" {
  let a = mk_tyvar("A")
  let x = mk_var("x", a)
  let y = mk_var("y", a)
  let z = mk_var("z", a)
  let t1 = mk_abs(x, mk_comb(x, y))
  let t2 = mk_abs(z, mk_comb(z, y))
  let t3 = mk_abs(z, mk_comb(y, z))

  assert_true(term_alpha_eq(t1, t2))
  assert_false(term_alpha_eq(t1, t3))
}
