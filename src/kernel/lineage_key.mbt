///|
/// Injective encodings used to build lineage events (#70).
///
/// The pretty printers are not injective: `Const("x", ty, 1)` and
/// `Const("x#1", ty, -1)` print the same text, so two different extensions
/// could intern to the same lineage node. Every encoder below is prefix-free
/// (each string is length-prefixed and each constructor has its own tag), so
/// the concatenation of encodings determines the encoded value.
fn key_str(s : String) -> String {
  s.length().to_string() + ":" + s
}

///|
fn key_int(n : Int32) -> String {
  n.to_string() + ";"
}

///|
fn ty_key(ty : HolType) -> String {
  match ty {
    TyVal(name) => "V" + key_str(name)
    TyApp(name, args) =>
      "A" + key_str(name) + key_int(args.length()) + args.map(ty_key).join("")
  }
}

///|
fn term_key(term : Term) -> String {
  match term {
    Var(name, ty) => "v" + key_str(name) + ty_key(ty)
    Const(name, ty, id) => "c" + key_str(name) + ty_key(ty) + key_int(id)
    Comb(f, x) => "a" + term_key(f) + term_key(x)
    Abs(v, body) => "l" + term_key(v) + term_key(body)
  }
}

///|
fn db_term_key(term : DbTerm) -> String {
  match term {
    DbBound(i, ty) => "b" + key_int(i) + ty_key(ty)
    DbFree(name, ty) => "f" + key_str(name) + ty_key(ty)
    DbConst(name, ty, id) => "c" + key_str(name) + ty_key(ty) + key_int(id)
    DbComb(f, x) => "a" + db_term_key(f) + db_term_key(x)
    DbAbs(ty, body) => "l" + ty_key(ty) + db_term_key(body)
  }
}

///|
fn thm_key(th : Thm) -> String {
  key_int(th.hyps.length()) +
  th.hyps.map(db_term_key).join("") +
  db_term_key(th.concl)
}
