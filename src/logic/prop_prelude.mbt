///|
pub struct PropRule {
  name : String
  premise_count : Int
}

///|
pub struct PropPrelude {
  imp_name : String
  not_name : String
  and_name : String
  or_name : String
  rules : Array[PropRule]
}

///|
pub fn default_prop_prelude() -> PropPrelude {
  PropPrelude::{
    imp_name: "imp",
    not_name: "not",
    and_name: "and",
    or_name: "or",
    rules: [
      PropRule::{ name: "imp_intro", premise_count: 1 },
      PropRule::{ name: "imp_elim", premise_count: 2 },
      PropRule::{ name: "and_intro", premise_count: 2 },
      PropRule::{ name: "and_elim_l", premise_count: 1 },
      PropRule::{ name: "and_elim_r", premise_count: 1 },
      PropRule::{ name: "or_intro_l", premise_count: 1 },
      PropRule::{ name: "or_intro_r", premise_count: 1 },
    ],
  }
}

///|
pub fn install_prop_prelude(
  state : KernelState,
) -> Result[KernelState, SigError] {
  let p = default_prop_prelude()
  let bool = bool_ty()
  let bool_unary = fun_ty(bool, bool)
  let bool_binary = fun_ty(bool, fun_ty(bool, bool))

  let s1 = match ks_add_const(state, p.not_name, bool_unary) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let s2 = match ks_add_const(s1, p.and_name, bool_binary) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let s3 = match ks_add_const(s2, p.or_name, bool_binary) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  ks_add_const(s3, p.imp_name, bool_binary)
}

///|
pub fn prop_prelude_rule_count(prelude : PropPrelude) -> Int {
  prelude.rules.length()
}

///|
pub fn prop_prelude_rule_at(prelude : PropPrelude, idx : Int) -> PropRule? {
  if idx < 0 || idx >= prelude.rules.length() {
    None
  } else {
    Some(prelude.rules[idx])
  }
}

///|
pub fn prop_prelude_has_rule(prelude : PropPrelude, name : String) -> Bool {
  prelude.rules.any(fn(rule) { rule.name == name })
}

///|
pub fn prop_mk_not(
  state : KernelState,
  prelude : PropPrelude,
  arg : Term,
) -> Result[Term, SigError] {
  match ks_mk_const(state, prelude.not_name) {
    Ok(c) => Ok(mk_comb(c, arg))
    Err(e) => Err(e)
  }
}

///|
pub fn prop_mk_imp(
  state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, SigError] {
  match ks_mk_const(state, prelude.imp_name) {
    Ok(c) => Ok(mk_comb(mk_comb(c, lhs), rhs))
    Err(e) => Err(e)
  }
}

///|
pub fn prop_mk_and(
  state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, SigError] {
  match ks_mk_const(state, prelude.and_name) {
    Ok(c) => Ok(mk_comb(mk_comb(c, lhs), rhs))
    Err(e) => Err(e)
  }
}

///|
pub fn prop_mk_or(
  state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, SigError] {
  match ks_mk_const(state, prelude.or_name) {
    Ok(c) => Ok(mk_comb(mk_comb(c, lhs), rhs))
    Err(e) => Err(e)
  }
}

///|
fn dest_binop_by_name(term : Term, op_name : String) -> (Term, Term)? {
  match dest_comb(term) {
    Some((f, rhs)) =>
      match dest_comb(f) {
        Some((head, lhs)) =>
          match dest_const(head) {
            Some((name, _)) if name == op_name => Some((lhs, rhs))
            _ => None
          }
        None => None
      }
    None => None
  }
}

///|
pub fn prop_dest_imp(prelude : PropPrelude, term : Term) -> (Term, Term)? {
  dest_binop_by_name(term, prelude.imp_name)
}

///|
pub fn prop_dest_and(prelude : PropPrelude, term : Term) -> (Term, Term)? {
  dest_binop_by_name(term, prelude.and_name)
}

///|
pub fn prop_dest_or(prelude : PropPrelude, term : Term) -> (Term, Term)? {
  dest_binop_by_name(term, prelude.or_name)
}

///|
pub fn prop_dest_not(prelude : PropPrelude, term : Term) -> Term? {
  match dest_comb(term) {
    Some((head, arg)) =>
      match dest_const(head) {
        Some((name, _)) if name == prelude.not_name => Some(arg)
        _ => None
      }
    None => None
  }
}

///|
pub fn logic_prop_prelude_phase0_ready() -> Bool {
  true
}
