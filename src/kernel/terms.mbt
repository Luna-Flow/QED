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
pub fn type_of(term : Term) -> HolType {
  match term {
    Var(_, ty) => ty
    Const(_, ty) => ty
    Comb(fn_term, _) =>
      match type_of(fn_term) {
        TyApp("fun", [_, cod]) => cod
        _ => bool_ty()
      }
    Abs(var_term, body) => fun_ty(type_of(var_term), type_of(body))
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
    (DbBound(i1, ty1), DbBound(i2, ty2)) =>
      i1 == i2 && hol_type_to_string(ty1) == hol_type_to_string(ty2)
    (DbFree(n1, ty1), DbFree(n2, ty2)) =>
      n1 == n2 && hol_type_to_string(ty1) == hol_type_to_string(ty2)
    (DbConst(n1, ty1), DbConst(n2, ty2)) =>
      n1 == n2 && hol_type_to_string(ty1) == hol_type_to_string(ty2)
    (DbComb(f1, x1), DbComb(f2, x2)) => db_term_eq(f1, f2) && db_term_eq(x1, x2)
    (DbAbs(ty1, b1), DbAbs(ty2, b2)) =>
      hol_type_to_string(ty1) == hol_type_to_string(ty2) && db_term_eq(b1, b2)
    _ => false
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
fn db_string_with_env(term : Term, env : Array[String]) -> String {
  match term {
    Var(name, ty) =>
      match lookup_db_index(env, name) {
        Some(i) =>
          "BVar(" + i.to_string() + " : " + hol_type_to_string(ty) + ")"
        None => "FVar(" + name + " : " + hol_type_to_string(ty) + ")"
      }
    Const(name, ty) => "Const(" + name + " : " + hol_type_to_string(ty) + ")"
    Comb(f, x) =>
      "Comb(" +
      db_string_with_env(f, env) +
      ", " +
      db_string_with_env(x, env) +
      ")"
    Abs(v, body) =>
      match v {
        Var(name, ty) => {
          let env2 = env.copy()
          env2.push(name)
          "Abs(" +
          hol_type_to_string(ty) +
          ". " +
          db_string_with_env(body, env2) +
          ")"
        }
        _ => "Abs(? . " + db_string_with_env(body, env) + ")"
      }
  }
}

///|
pub fn db_string(term : Term) -> String {
  db_string_with_env(term, [])
}
