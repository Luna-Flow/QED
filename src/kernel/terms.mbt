///|
/// HOL term representation used by the trusted kernel.
pub enum Term {
  Var(String, HolType)
  Const(String, HolType)
  Comb(Term, Term)
  Abs(Term, Term)
}

///|
/// Explicit De Bruijn representation used for alpha-invariant analyses.
pub enum DbTerm {
  DbBound(Int, HolType)
  DbFree(String, HolType)
  DbConst(String, HolType)
  DbComb(DbTerm, DbTerm)
  DbAbs(HolType, DbTerm)
}

///|
/// Constructors
pub fn mk_var(name : String, ty : HolType) -> Term {
  Var(name, ty)
}

///|
pub fn mk_const(name : String, ty : HolType) -> Term {
  Const(name, ty)
}

///|
pub fn mk_comb(fn_term : Term, arg_term : Term) -> Term {
  Comb(fn_term, arg_term)
}

///|
pub fn mk_abs(var_term : Term, body : Term) -> Term {
  Abs(var_term, body)
}

///|
/// Predicates
pub fn is_var(term : Term) -> Bool {
  match term {
    Var(_, _) => true
    _ => false
  }
}

///|
pub fn is_const(term : Term) -> Bool {
  match term {
    Const(_, _) => true
    _ => false
  }
}

///|
pub fn is_comb(term : Term) -> Bool {
  match term {
    Comb(_, _) => true
    _ => false
  }
}

///|
pub fn is_abs(term : Term) -> Bool {
  match term {
    Abs(_, _) => true
    _ => false
  }
}

///|
/// Destructors
pub fn dest_var(term : Term) -> (String, HolType)? {
  match term {
    Var(name, ty) => Some((name, ty))
    _ => None
  }
}

///|
pub fn dest_const(term : Term) -> (String, HolType)? {
  match term {
    Const(name, ty) => Some((name, ty))
    _ => None
  }
}

///|
pub fn dest_comb(term : Term) -> (Term, Term)? {
  match term {
    Comb(fn_term, arg_term) => Some((fn_term, arg_term))
    _ => None
  }
}

///|
pub fn dest_abs(term : Term) -> (Term, Term)? {
  match term {
    Abs(var_term, body) => Some((var_term, body))
    _ => None
  }
}

///|
/// Returns the type of a term.
pub fn type_of(term : Term) -> HolType? {
  match term {
    Var(_, ty) => Some(ty)
    Const(_, ty) => Some(ty)
    Comb(fn_term, arg_term) =>
      match (type_of(fn_term), type_of(arg_term)) {
        (Some(TyApp("fun", [dom, cod])), Some(arg_ty)) =>
          if ty_eq(dom, arg_ty) {
            Some(cod)
          } else {
            None
          }
        _ => None
      }
    Abs(var_term, body) =>
      match var_term {
        Var(_, ty) =>
          match type_of(body) {
            Some(body_ty) => Some(fun_ty(ty, body_ty))
            None => None
          }
        _ => None
      }
  }
}

///|
pub fn kernel_terms_phase0_ready() -> Bool {
  true
}

///|
/// Pretty printer for debug and test output.
pub fn term_to_string(term : Term) -> String {
  match term {
    Var(name, ty) => "Var(" + name + " : " + hol_type_to_string(ty) + ")"
    Const(name, ty) => "Const(" + name + " : " + hol_type_to_string(ty) + ")"
    Comb(fn_term, arg_term) =>
      "Comb(" + term_to_string(fn_term) + ", " + term_to_string(arg_term) + ")"
    Abs(var_term, body) =>
      "Abs(" + term_to_string(var_term) + ", " + term_to_string(body) + ")"
  }
}

///|
fn lookup_db_index(stack : Array[String], name : String) -> Int? {
  let mut i = 0
  let n = stack.length()
  while i < n {
    let idx = n - 1 - i
    if stack[idx] == name {
      return Some(i)
    }
    i = i + 1
  }
  None
}

///|
fn to_db_term_with_env(term : Term, env : Array[String]) -> DbTerm? {
  match term {
    Var(name, ty) =>
      match lookup_db_index(env, name) {
        Some(i) => Some(DbBound(i, ty))
        None => Some(DbFree(name, ty))
      }
    Const(name, ty) => Some(DbConst(name, ty))
    Comb(f, x) =>
      match (to_db_term_with_env(f, env), to_db_term_with_env(x, env)) {
        (Some(f2), Some(x2)) => Some(DbComb(f2, x2))
        _ => None
      }
    Abs(v, body) =>
      match v {
        Var(name, ty) => {
          let env2 = env.copy()
          env2.push(name)
          match to_db_term_with_env(body, env2) {
            Some(body2) => Some(DbAbs(ty, body2))
            None => None
          }
        }
        _ => None
      }
  }
}

///|
pub fn to_db_term(term : Term) -> DbTerm? {
  to_db_term_with_env(term, [])
}

///|
fn collect_db_free_names(term : DbTerm, out : Array[String]) -> Unit {
  match term {
    DbBound(_, _) => ()
    DbFree(name, _) => if !out.contains(name) { out.push(name) }
    DbConst(_, _) => ()
    DbComb(f, x) => {
      collect_db_free_names(f, out)
      collect_db_free_names(x, out)
    }
    DbAbs(_, body) => collect_db_free_names(body, out)
  }
}

///|
fn fresh_bound_name(
  forbidden : Array[String],
  used : Array[String],
  seed : Int,
) -> String {
  let mut i = seed
  while true {
    let candidate = "_b" + i.to_string()
    if !forbidden.contains(candidate) && !used.contains(candidate) {
      return candidate
    }
    i = i + 1
  }
  "_b0"
}

///|
fn from_db_term_with_env(
  term : DbTerm,
  env : Array[(String, HolType)],
  forbidden : Array[String],
  used : Array[String],
) -> Term? {
  match term {
    DbBound(i, ty) => {
      let n = env.length()
      if i < 0 || i >= n {
        None
      } else {
        let (name, ty2) = env[n - 1 - i]
        if ty_eq(ty, ty2) {
          Some(Var(name, ty))
        } else {
          None
        }
      }
    }
    DbFree(name, ty) => Some(Var(name, ty))
    DbConst(name, ty) => Some(Const(name, ty))
    DbComb(f, x) =>
      match
        (
          from_db_term_with_env(f, env, forbidden, used),
          from_db_term_with_env(x, env, forbidden, used),
        ) {
        (Some(f2), Some(x2)) => Some(Comb(f2, x2))
        _ => None
      }
    DbAbs(ty, body) => {
      let name = fresh_bound_name(forbidden, used, used.length())
      let env2 = env.copy()
      env2.push((name, ty))
      let used2 = used.copy()
      used2.push(name)
      match from_db_term_with_env(body, env2, forbidden, used2) {
        Some(body2) => Some(Abs(Var(name, ty), body2))
        None => None
      }
    }
  }
}

///|
pub fn from_db_term(term : DbTerm) -> Term? {
  let forbidden : Array[String] = []
  collect_db_free_names(term, forbidden)
  from_db_term_with_env(term, [], forbidden, [])
}

///|
pub fn term_alpha_eq(lhs : Term, rhs : Term) -> Bool {
  match (to_db_term(lhs), to_db_term(rhs)) {
    (Some(d1), Some(d2)) => db_term_eq(d1, d2)
    _ => false
  }
}

///|
pub fn db_term_to_string(term : DbTerm) -> String {
  match term {
    DbBound(i, ty) =>
      "BVar(" + i.to_string() + " : " + hol_type_to_string(ty) + ")"
    DbFree(name, ty) => "FVar(" + name + " : " + hol_type_to_string(ty) + ")"
    DbConst(name, ty) => "Const(" + name + " : " + hol_type_to_string(ty) + ")"
    DbComb(f, x) =>
      "Comb(" + db_term_to_string(f) + ", " + db_term_to_string(x) + ")"
    DbAbs(ty, body) =>
      "Abs(" + hol_type_to_string(ty) + ". " + db_term_to_string(body) + ")"
  }
}

///|
pub fn db_term_eq(lhs : DbTerm, rhs : DbTerm) -> Bool {
  match (lhs, rhs) {
    (DbBound(i1, ty1), DbBound(i2, ty2)) => i1 == i2 && ty_eq(ty1, ty2)
    (DbFree(n1, ty1), DbFree(n2, ty2)) => n1 == n2 && ty_eq(ty1, ty2)
    (DbConst(n1, ty1), DbConst(n2, ty2)) => n1 == n2 && ty_eq(ty1, ty2)
    (DbComb(f1, x1), DbComb(f2, x2)) => db_term_eq(f1, f2) && db_term_eq(x1, x2)
    (DbAbs(ty1, b1), DbAbs(ty2, b2)) => ty_eq(ty1, ty2) && db_term_eq(b1, b2)
    _ => false
  }
}

///|
pub fn db_has_free(term : DbTerm, needle : DbTerm) -> Bool {
  match term {
    DbBound(_, _) => false
    DbFree(_, _) => db_term_eq(term, needle)
    DbConst(_, _) => false
    DbComb(f, x) => db_has_free(f, needle) || db_has_free(x, needle)
    DbAbs(_, body) => db_has_free(body, needle)
  }
}

///|
fn db_shift_walk(delta : Int, cutoff : Int, term : DbTerm) -> DbTerm {
  match term {
    DbBound(i, ty) => if i >= cutoff { DbBound(i + delta, ty) } else { term }
    DbFree(_, _) => term
    DbConst(_, _) => term
    DbComb(f, x) =>
      DbComb(db_shift_walk(delta, cutoff, f), db_shift_walk(delta, cutoff, x))
    DbAbs(ty, body) => DbAbs(ty, db_shift_walk(delta, cutoff + 1, body))
  }
}

///|
fn db_subst_walk(j : Int, s : DbTerm, cutoff : Int, term : DbTerm) -> DbTerm {
  match term {
    DbBound(i, _) =>
      if i == j + cutoff {
        db_shift_walk(cutoff, 0, s)
      } else {
        term
      }
    DbFree(_, _) => term
    DbConst(_, _) => term
    DbComb(f, x) =>
      DbComb(db_subst_walk(j, s, cutoff, f), db_subst_walk(j, s, cutoff, x))
    DbAbs(ty, body) => DbAbs(ty, db_subst_walk(j, s, cutoff + 1, body))
  }
}

///|
fn lookup_db_subst(subst : Array[(DbTerm, DbTerm)], key : DbTerm) -> DbTerm? {
  for entry in subst {
    let (k, v) = entry
    if db_term_eq(k, key) {
      return Some(v)
    }
  }
  None
}

///|
fn lookup_ty_subst_term(
  subst : Array[(String, HolType)],
  name : String,
) -> HolType? {
  for kv in subst {
    let (k, v) = kv
    if k == name {
      return Some(v)
    }
  }
  None
}

///|
fn db_apply_ty_subst_to_type(
  subst : Array[(String, HolType)],
  ty : HolType,
) -> HolType {
  match ty {
    TyVal(name) =>
      match lookup_ty_subst_term(subst, name) {
        Some(t) => t
        None => ty
      }
    TyApp(tycon, args) =>
      TyApp(tycon, args.map(fn(a) { db_apply_ty_subst_to_type(subst, a) }))
  }
}

///|
pub fn db_apply_ty_subst(
  subst : Array[(String, HolType)],
  term : DbTerm,
) -> DbTerm {
  match term {
    DbBound(i, ty) => DbBound(i, db_apply_ty_subst_to_type(subst, ty))
    DbFree(name, ty) => DbFree(name, db_apply_ty_subst_to_type(subst, ty))
    DbConst(name, ty) => DbConst(name, db_apply_ty_subst_to_type(subst, ty))
    DbComb(f, x) =>
      DbComb(db_apply_ty_subst(subst, f), db_apply_ty_subst(subst, x))
    DbAbs(ty, body) =>
      DbAbs(
        db_apply_ty_subst_to_type(subst, ty),
        db_apply_ty_subst(subst, body),
      )
  }
}

///|
pub fn db_subst_free_parallel(
  term : DbTerm,
  subst : Array[(DbTerm, DbTerm)],
) -> DbTerm {
  fn walk(depth : Int, t : DbTerm, subst : Array[(DbTerm, DbTerm)]) -> DbTerm {
    match t {
      DbBound(_, _) => t
      DbFree(_, _) =>
        match lookup_db_subst(subst, t) {
          Some(repl) => db_shift_walk(depth, 0, repl)
          None => t
        }
      DbConst(_, _) => t
      DbComb(f, x) => DbComb(walk(depth, f, subst), walk(depth, x, subst))
      DbAbs(ty, body) => DbAbs(ty, walk(depth + 1, body, subst))
    }
  }

  walk(0, term, subst)
}

///|
pub fn db_type_of(term : DbTerm) -> HolType? {
  match term {
    DbBound(_, ty) => Some(ty)
    DbFree(_, ty) => Some(ty)
    DbConst(_, ty) => Some(ty)
    DbComb(f, arg) =>
      match (db_type_of(f), db_type_of(arg)) {
        (Some(TyApp("fun", [dom, cod])), Some(arg_ty)) =>
          if ty_eq(dom, arg_ty) {
            Some(cod)
          } else {
            None
          }
        _ => None
      }
    DbAbs(ty, body) =>
      match db_type_of(body) {
        Some(body_ty) => Some(fun_ty(ty, body_ty))
        None => None
      }
  }
}

///|
pub fn db_beta_reduce_once(term : DbTerm) -> DbTerm? {
  match term {
    DbComb(DbAbs(_, body), arg) => {
      let arg1 = db_shift_walk(1, 0, arg)
      let body1 = db_subst_walk(0, arg1, 0, body)
      Some(db_shift_walk(-1, 0, body1))
    }
    _ => None
  }
}

///|
fn vars_contains(
  vars : Array[(String, HolType)],
  item : (String, HolType),
) -> Bool {
  let (name, ty) = item
  for pair in vars {
    let (name2, ty2) = pair
    if name == name2 && ty_eq(ty, ty2) {
      return true
    }
  }
  false
}

///|
fn vars_union(
  a : Array[(String, HolType)],
  b : Array[(String, HolType)],
) -> Array[(String, HolType)] {
  let out = a.copy()
  for item in b {
    if !vars_contains(out, item) {
      out.push(item)
    }
  }
  out
}

///|
pub fn free_vars(term : Term) -> Array[(String, HolType)] {
  match term {
    Var(name, ty) => [(name, ty)]
    Const(_, _) => []
    Comb(f, x) => vars_union(free_vars(f), free_vars(x))
    Abs(var_term, body) =>
      match var_term {
        Var(name, ty) => {
          let body_vars = free_vars(body)
          body_vars.filter(fn(item) {
            let (name2, ty2) = item
            !(name == name2 && ty_eq(ty, ty2))
          })
        }
        _ => free_vars(body)
      }
  }
}

///|
pub fn term_is_closed(term : Term) -> Bool {
  free_vars(term).length() == 0
}

///|
pub fn term_has_const_named(term : Term, name : String) -> Bool {
  match term {
    Var(_, _) => false
    Const(n, _) => n == name
    Comb(f, x) => term_has_const_named(f, name) || term_has_const_named(x, name)
    Abs(_, body) => term_has_const_named(body, name)
  }
}

///|
pub fn term_apply_ty_subst(
  subst : Array[(String, HolType)],
  term : Term,
) -> Term? {
  if has_duplicate_ty_subst_keys(subst) {
    return None
  }
  Some(term_apply_ty_subst_unsafe(subst, term))
}

///|
pub fn term_apply_ty_subst_unsafe(
  subst : Array[(String, HolType)],
  term : Term,
) -> Term {
  let rew_ty = fn(ty : HolType) { type_subst_unsafe(subst, ty) }
  match term {
    Var(name, ty) => Var(name, rew_ty(ty))
    Const(name, ty) => Const(name, rew_ty(ty))
    Comb(f, x) =>
      Comb(
        term_apply_ty_subst_unsafe(subst, f),
        term_apply_ty_subst_unsafe(subst, x),
      )
    Abs(v, body) =>
      Abs(
        term_apply_ty_subst_unsafe(subst, v),
        term_apply_ty_subst_unsafe(subst, body),
      )
  }
}

///|
fn push_unique_string(out : Array[String], v : String) -> Unit {
  if !out.contains(v) {
    out.push(v)
  }
}

///|
fn union_strings(a : Array[String], b : Array[String]) -> Array[String] {
  let out = a.copy()
  b.each(fn(v) { push_unique_string(out, v) })
  out
}

///|
fn term_tyvars_impl(term : Term) -> Array[String] {
  match term {
    Var(_, ty) => tyvars(ty)
    Const(_, ty) => tyvars(ty)
    Comb(f, x) => union_strings(term_tyvars_impl(f), term_tyvars_impl(x))
    Abs(v, body) => union_strings(term_tyvars_impl(v), term_tyvars_impl(body))
  }
}

///|
pub fn term_tyvars(term : Term) -> Array[String] {
  term_tyvars_impl(term)
}

///|
pub fn term_tyvars_subset(term : Term, ty : HolType) -> Bool {
  let rhs = term_tyvars(term)
  let lhs = tyvars(ty)
  rhs.all(fn(v) { lhs.contains(v) })
}
