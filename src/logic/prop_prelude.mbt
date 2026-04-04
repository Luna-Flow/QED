///|
pub struct PropRule {
  name : String
  premise_count : Int
}

///|
pub struct PropPrelude {
  truth_name : String
  false_name : String
  imp_name : String
  not_name : String
  and_name : String
  or_name : String
  rules : Array[PropRule]
}

///|
pub fn default_prop_prelude() -> PropPrelude {
  PropPrelude::{
    truth_name: "T",
    false_name: "F",
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
fn require_bool_term(term : Term) -> Result[Unit, LogicError] {
  match type_of(term) {
    Some(ty) =>
      if ty_eq(ty, bool_ty()) {
        Ok(())
      } else {
        Err(prop_not_bool_term())
      }
    None => Err(prop_type_mismatch())
  }
}

///|
fn prop_const_type_conflict() -> SigError {
  let st0 = empty_kernel_state()
  let st1 = match ks_add_const(st0, "_prop_conflict", bool_ty()) {
    Ok(v) => v
    Err(_) => panic()
  }
  match ks_add_const(st1, "_prop_conflict", fun_ty(bool_ty(), bool_ty())) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn prop_definition_already_exists() -> SigError {
  let st0 = empty_kernel_state()
  let (st1, _) = match
    ks_define_const_thm(st0, "_prop_dup", bool_ty(), prop_truth_term()) {
    Ok(v) => v
    Err(_) => panic()
  }
  match ks_define_const_thm(st1, "_prop_dup", bool_ty(), prop_truth_term()) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn prop_not_bool_term() -> LogicError {
  let x = mk_var("_p_not_bool", mk_tyvar("_PNotBool"))
  match assume_checked(empty_kernel_state(), x) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn prop_type_mismatch() -> LogicError {
  match
    mk_eq(mk_var("_p_tm_l", bool_ty()), mk_var("_p_tm_r", mk_tyvar("_PTM"))) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn prop_truth_term() -> Term {
  let x = mk_var("_p_true", bool_ty())
  let id = mk_abs(x, x)
  match mk_eq(id, id) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn prop_truth_fn_term() -> Term {
  let x = mk_var("_p_truth_fn", bool_ty())
  mk_abs(x, prop_truth_term())
}

///|
fn prop_false_term() -> Term {
  let p = mk_var("_p_false", bool_ty())
  let pred = mk_abs(p, p)
  match mk_eq(pred, prop_truth_fn_term()) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn prop_and_term(lhs : Term, rhs : Term) -> Term {
  let bool = bool_ty()
  let bool_binary = fun_ty(bool, fun_ty(bool, bool))
  let f = mk_var("_p_and", bool_binary)
  let lhs_fun = mk_abs(f, mk_comb(mk_comb(f, lhs), rhs))
  let t = prop_truth_term()
  let rhs_fun = mk_abs(f, mk_comb(mk_comb(f, t), t))
  match mk_eq(lhs_fun, rhs_fun) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn prop_imp_term(lhs : Term, rhs : Term) -> Term {
  match mk_eq(prop_and_term(lhs, rhs), lhs) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn prop_not_term(arg : Term) -> Term {
  prop_imp_term(arg, prop_false_term())
}

///|
fn prop_or_term(lhs : Term, rhs : Term) -> Term {
  prop_imp_term(prop_not_term(lhs), rhs)
}

///|
fn ensure_defined_const(
  state : KernelState,
  name : String,
  decl_ty : HolType,
  rhs : Term,
) -> Result[KernelState, SigError] {
  let current_id = match ks_lookup_const_id(state, name) {
    Some(id) => Some(id)
    None => None
  }
  let current_def_matches = fn() {
    let id = match current_id {
      Some(v) => v
      None => return false
    }
    let def_th = match ks_definition_theorem(state, name) {
      Ok(v) => v
      Err(_) => return false
    }
    let concl = match thm_concl(def_th) {
      Ok(v) => v
      Err(_) => return false
    }
    let (lhs, rhs0) = match dest_eq(concl) {
      Ok(v) => v
      Err(_) => return false
    }
    match lhs {
      Const(lhs_name, lhs_ty, lhs_id) =>
        lhs_name == name &&
        lhs_id == id &&
        ty_eq(lhs_ty, decl_ty) &&
        term_alpha_eq(rhs0, rhs)
      _ => false
    }
  }
  match ks_lookup_const(state, name) {
    Some(existing) =>
      if ty_eq(existing, decl_ty) {
        if current_def_matches() {
          Ok(state)
        } else {
          Err(prop_definition_already_exists())
        }
      } else {
        Err(prop_const_type_conflict())
      }
    None =>
      match ks_define_const_thm(state, name, decl_ty, rhs) {
        Ok((st2, _)) => Ok(st2)
        Err(e) => Err(e)
      }
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

  let s0 = match
    ensure_defined_const(state, p.truth_name, bool, prop_truth_term()) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let s0b = match
    ensure_defined_const(s0, p.false_name, bool, prop_false_term()) {
    Ok(v) => v
    Err(e) => return Err(e)
  }

  let pv = mk_var("_p", bool)
  let qv = mk_var("_q", bool)
  let s1 = match
    ensure_defined_const(
      s0b,
      p.and_name,
      bool_binary,
      mk_abs(pv, mk_abs(qv, prop_and_term(pv, qv))),
    ) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let imp_l = mk_var("_p_imp_l", bool)
  let imp_r = mk_var("_p_imp_r", bool)
  let s2 = match
    ensure_defined_const(
      s1,
      p.imp_name,
      bool_binary,
      mk_abs(imp_l, mk_abs(imp_r, prop_imp_term(imp_l, imp_r))),
    ) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let not_p = mk_var("_p_not", bool)
  let s3 = match
    ensure_defined_const(
      s2,
      p.not_name,
      bool_unary,
      mk_abs(not_p, prop_not_term(not_p)),
    ) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let or_l = mk_var("_p_or_l", bool)
  let or_r = mk_var("_p_or_r", bool)
  ensure_defined_const(
    s3,
    p.or_name,
    bool_binary,
    mk_abs(or_l, mk_abs(or_r, prop_or_term(or_l, or_r))),
  )
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
pub fn prop_truth_name(prelude : PropPrelude) -> String {
  prelude.truth_name
}

///|
pub fn prop_false_name(prelude : PropPrelude) -> String {
  prelude.false_name
}

///|
pub fn prop_mk_not(
  _state : KernelState,
  prelude : PropPrelude,
  arg : Term,
) -> Result[Term, LogicError] {
  let _ = prelude
  match require_bool_term(arg) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  Ok(prop_not_term(arg))
}

///|
pub fn prop_mk_imp(
  _state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, LogicError] {
  let _ = prelude
  match require_bool_term(lhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  match require_bool_term(rhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  Ok(prop_imp_term(lhs, rhs))
}

///|
pub fn prop_mk_and(
  _state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, LogicError] {
  let _ = prelude
  match require_bool_term(lhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  match require_bool_term(rhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  Ok(prop_and_term(lhs, rhs))
}

///|
pub fn prop_mk_or(
  _state : KernelState,
  prelude : PropPrelude,
  lhs : Term,
  rhs : Term,
) -> Result[Term, LogicError] {
  let _ = prelude
  match require_bool_term(lhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  match require_bool_term(rhs) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  Ok(prop_or_term(lhs, rhs))
}

///|
fn trusted_binop_definition(
  state : KernelState,
  op_name : String,
  op_ty : HolType,
  rhs : Term,
) -> (ConstId, HolType)? {
  let current_id = match ks_lookup_const_id(state, op_name) {
    Some(v) => v
    None => return None
  }
  let def_th = match ks_definition_theorem(state, op_name) {
    Ok(v) => v
    Err(_) => return None
  }
  let concl = match thm_concl(def_th) {
    Ok(v) => v
    Err(_) => return None
  }
  let (lhs, rhs0) = match dest_eq(concl) {
    Ok(v) => v
    Err(_) => return None
  }
  match lhs {
    Const(lhs_name, lhs_ty, lhs_id) =>
      if lhs_name == op_name &&
        lhs_id == current_id &&
        ty_eq(lhs_ty, op_ty) &&
        term_alpha_eq(rhs0, rhs) {
        Some((current_id, lhs_ty))
      } else {
        None
      }
    _ => None
  }
}

///|
fn dest_trusted_binop(
  state : KernelState,
  op_name : String,
  op_ty : HolType,
  expected_rhs : Term,
  term : Term,
) -> (Term, Term)? {
  match dest_comb(term) {
    Some((f, rhs_term)) =>
      match dest_comb(f) {
        Some((head, lhs)) =>
          match
            (
              head,
              trusted_binop_definition(state, op_name, op_ty, expected_rhs),
            ) {
            (Const(name, head_ty, head_id), Some((trusted_id, trusted_ty))) =>
              if name == op_name &&
                head_id == trusted_id &&
                ty_eq(head_ty, trusted_ty) {
                Some((lhs, rhs_term))
              } else {
                None
              }
            _ => None
          }
        None => None
      }
    None => None
  }
}

///|
fn canonical_dest_imp(_prelude : PropPrelude, term : Term) -> (Term, Term)? {
  match dest_eq(term) {
    Ok((lhs_eq, rhs)) =>
      match canonical_dest_and(lhs_eq) {
        Some((a, b)) if term_alpha_eq(rhs, a) => Some((a, b))
        _ => None
      }
    Err(_) => None
  }
}

///|
fn canonical_dest_and(term : Term) -> (Term, Term)? {
  match dest_eq(term) {
    Ok((lhs_fun, rhs_fun)) =>
      match (dest_abs(lhs_fun), dest_abs(rhs_fun)) {
        (Some((f1, lhs_body)), Some((f2, rhs_body))) =>
          match (dest_comb(lhs_body), dest_comb(rhs_body)) {
            (Some((lhs_head, rhs_arg)), Some((rhs_head, rhs_tail))) =>
              match (dest_comb(lhs_head), dest_comb(rhs_head)) {
                (Some((lhs_var, lhs_arg)), Some((rhs_var, rhs_arg1))) =>
                  if term_alpha_eq(lhs_var, f1) &&
                    term_alpha_eq(rhs_var, f2) &&
                    term_alpha_eq(rhs_arg1, prop_truth_term()) &&
                    term_alpha_eq(rhs_tail, prop_truth_term()) {
                    Some((lhs_arg, rhs_arg))
                  } else {
                    None
                  }
                _ => None
              }
            _ => None
          }
        _ => None
      }
    Err(_) => None
  }
}

///|
fn canonical_dest_or(prelude : PropPrelude, term : Term) -> (Term, Term)? {
  match canonical_dest_imp(prelude, term) {
    Some((lhs, rhs)) =>
      match canonical_dest_not(prelude, lhs) {
        Some(inner) => Some((inner, rhs))
        None => None
      }
    None => None
  }
}

///|
fn canonical_dest_not(prelude : PropPrelude, term : Term) -> Term? {
  match canonical_dest_imp(prelude, term) {
    Some((arg2, rhs)) if term_alpha_eq(rhs, prop_false_term()) => Some(arg2)
    _ => None
  }
}

///|
pub fn prop_dest_imp(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> (Term, Term)? {
  let _ = prelude
  let bool = bool_ty()
  let bool_binary = fun_ty(bool, fun_ty(bool, bool))
  let imp_l = mk_var("_p_imp_l", bool)
  let imp_r = mk_var("_p_imp_r", bool)
  match
    dest_trusted_binop(
      state,
      prelude.imp_name,
      bool_binary,
      mk_abs(imp_l, mk_abs(imp_r, prop_imp_term(imp_l, imp_r))),
      term,
    ) {
    Some(v) => Some(v)
    None => canonical_dest_imp(prelude, term)
  }
}

///|
pub fn prop_dest_and(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> (Term, Term)? {
  let _ = prelude
  let bool = bool_ty()
  let bool_binary = fun_ty(bool, fun_ty(bool, bool))
  let pv = mk_var("_p", bool)
  let qv = mk_var("_q", bool)
  match
    dest_trusted_binop(
      state,
      prelude.and_name,
      bool_binary,
      mk_abs(pv, mk_abs(qv, prop_and_term(pv, qv))),
      term,
    ) {
    Some(v) => Some(v)
    None => canonical_dest_and(term)
  }
}

///|
pub fn prop_dest_or(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> (Term, Term)? {
  let bool = bool_ty()
  let bool_binary = fun_ty(bool, fun_ty(bool, bool))
  let or_l = mk_var("_p_or_l", bool)
  let or_r = mk_var("_p_or_r", bool)
  match
    dest_trusted_binop(
      state,
      prelude.or_name,
      bool_binary,
      mk_abs(or_l, mk_abs(or_r, prop_or_term(or_l, or_r))),
      term,
    ) {
    Some(v) => Some(v)
    None => canonical_dest_or(prelude, term)
  }
}

///|
pub fn prop_dest_not(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> Term? {
  let bool = bool_ty()
  let bool_unary = fun_ty(bool, bool)
  let not_p = mk_var("_p_not", bool)
  match dest_comb(term) {
    Some((head, arg)) =>
      match
        (
          head,
          trusted_binop_definition(
            state,
            prelude.not_name,
            bool_unary,
            mk_abs(not_p, prop_not_term(not_p)),
          ),
        ) {
        (Const(name, head_ty, head_id), Some((trusted_id, trusted_ty))) =>
          if name == prelude.not_name &&
            head_id == trusted_id &&
            ty_eq(head_ty, trusted_ty) {
            Some(arg)
          } else {
            canonical_dest_not(prelude, term)
          }
        _ => canonical_dest_not(prelude, term)
      }
    None => canonical_dest_not(prelude, term)
  }
}
