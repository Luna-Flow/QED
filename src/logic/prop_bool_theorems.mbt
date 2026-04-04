///|
fn logic_bool_type_mismatch() -> LogicError {
  match mk_eq(mk_var("_lbt_a", bool_ty()), mk_var("_lbt_b", mk_tyvar("_LBT"))) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn selector_left_term() -> Term {
  let x = mk_var("_sel_l_x", bool_ty())
  let y = mk_var("_sel_l_y", bool_ty())
  mk_abs(x, mk_abs(y, x))
}

///|
fn selector_right_term() -> Term {
  let x = mk_var("_sel_r_x", bool_ty())
  let y = mk_var("_sel_r_y", bool_ty())
  mk_abs(x, mk_abs(y, y))
}

///|
/// ⊢ λf. f T T = λf. f t t, with `T` the prelude truth constant and `t` the shallow
/// truth atom (the rhs of `T`'s definition).
fn logic_prop_conj_tt_abs_eq_thm(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, LogicError] {
  let th_def_t = match ks_definition_theorem(state, prelude.truth_name) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let f = mk_var("_conj_abs_f", fun_ty(bool_ty(), fun_ty(bool_ty(), bool_ty())))
  let th_f = match logic_refl(state, f) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_a = match logic_mk_comb_rule(state, th_f, th_def_t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_b = match logic_mk_comb_rule(state, th_a, th_def_t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_abs_rule(state, f, th_b)
}

///|
/// ⊢ (/\) T T in combinator form (no hypotheses).
fn logic_prop_comb_and_tt_thm(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, LogicError] {
  let t = match ks_mk_const(state, prelude.truth_name) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let and_c = match ks_mk_const(state, prelude.and_name) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let comb_exp = mk_comb(mk_comb(and_c, t), t)
  let th_def_and = match logic_prop_def_and(state, prelude) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th0 = match logic_apply_fun_eq2(state, th_def_and, t, t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eq = match logic_beta_normalize_eq_full(state, th0) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (lhs, _) = match thm_concl(th_eq) {
    Ok(c) =>
      match dest_eq(c) {
        Ok(pair) => pair
        Err(_) => return Err(logic_bool_type_mismatch())
      }
    Err(e) => return Err(e)
  }
  if !term_logical_eq(lhs, comb_exp) {
    return Err(logic_bool_type_mismatch())
  }
  let th_embed = match logic_prop_conj_tt_abs_eq_thm(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_sym = match logic_eq_sym(state, th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_sym, th_embed)
}

///|
fn theorem_concl(th : Thm) -> Result[Term, LogicError] {
  thm_concl(th)
}

///|
fn theorem_has_hyp(th : Thm, term : Term) -> Result[Bool, LogicError] {
  match thm_hyps(th) {
    Ok(hs) => Ok(hs.any(fn(h) { term_logical_eq(h, term) }))
    Err(e) => Err(e)
  }
}

///|
/// HOL-Light `EQT_INTRO` / `CONJ` scaffolding: from `Γ ⊢ p` derive `Γ ⊢ p = T`
/// using `DEDUCT_ANTISYM` against `⊢ T`.
fn theorem_eq_to_truth(
  state : KernelState,
  prelude : PropPrelude,
  th_p : Thm,
) -> Result[Thm, LogicError] {
  let th_t = match logic_prop_truth_const_thm(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_deduct_antisym(state, th_p, th_t)
}

///|
fn theorem_ex_falso(
  state : KernelState,
  prelude : PropPrelude,
  th_false : Thm,
  target : Term,
) -> Result[Thm, LogicError] {
  let c = match thm_concl(th_false) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_expand = match dest_eq(c) {
    Ok(_) => th_false
    Err(_) => {
      let th_def_f = match ks_definition_theorem(state, prelude.false_name) {
        Ok(v) => v
        Err(_) => return Err(logic_bool_type_mismatch())
      }
      match logic_eq_mp_bool(state, th_def_f, th_false) {
        Ok(t) => t
        Err(_) => {
          let th_sym = match logic_eq_sym(state, th_def_f) {
            Ok(v) => v
            Err(e) => return Err(e)
          }
          match logic_eq_mp_bool(state, th_sym, th_false) {
            Ok(t) => t
            Err(e) => return Err(e)
          }
        }
      }
    }
  }
  let th_arg = match logic_refl(state, target) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_app = match logic_mk_comb_rule(state, th_expand, th_arg) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_norm = match logic_beta_normalize_eq_full(state, th_app) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_sym = match logic_eq_sym(state, th_norm) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_t = match logic_prop_truth_thm(state) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_sym, th_t)
}

///|
pub fn logic_prop_ex_falso_thm(
  state : KernelState,
  prelude : PropPrelude,
  th_false : Thm,
  target : Term,
) -> Result[Thm, LogicError] {
  theorem_ex_falso(state, prelude, th_false, target)
}

///|
pub fn logic_bool_false_def_thm(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, SigError] {
  ks_definition_theorem(state, prelude.false_name)
}

///|
pub fn logic_prop_and_intro_thm(
  state : KernelState,
  prelude : PropPrelude,
  th_p : Thm,
  th_q : Thm,
) -> Result[Thm, LogicError] {
  let p = match theorem_concl(th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let q = match theorem_concl(th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_p_eq_t = match theorem_eq_to_truth(state, prelude, th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q_eq_t = match theorem_eq_to_truth(state, prelude, th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let and_c = match ks_mk_const(state, prelude.and_name) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th_and_c = match logic_refl(state, and_c) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th1 = match logic_mk_comb_rule(state, th_and_c, th_p_eq_t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th2 = match logic_mk_comb_rule(state, th1, th_q_eq_t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_comb_tt = match logic_prop_comb_and_tt_thm(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th2_sym = match logic_eq_sym(state, th2) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_head = match logic_eq_mp_bool(state, th2_sym, th_comb_tt) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th3 = match logic_prop_unfold_and(state, prelude, th_head) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th4 = match logic_normalize_prop_beta(state, th3) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let and_term = match prop_mk_and(state, prelude, p, q) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let concl = match theorem_concl(th4) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_logical_eq(concl, and_term) {
    return Err(logic_bool_type_mismatch())
  }
  Ok(th4)
}

///|
pub fn logic_prop_and_elim_l_thm(
  state : KernelState,
  _prelude : PropPrelude,
  th_and : Thm,
) -> Result[Thm, LogicError] {
  let th_app = match logic_apply_fun_eq(state, th_and, selector_left_term()) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th1 = match logic_beta_normalize_eq_full(state, th_app) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th2 = match logic_eq_sym(state, th1) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th3 = match logic_beta_normalize_eq_full(state, th2) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_t = match logic_prop_truth_thm(state) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th3, th_t)
}

///|
pub fn logic_prop_and_elim_r_thm(
  state : KernelState,
  _prelude : PropPrelude,
  th_and : Thm,
) -> Result[Thm, LogicError] {
  let th_app = match logic_apply_fun_eq(state, th_and, selector_right_term()) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th1 = match logic_beta_normalize_eq_full(state, th_app) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th2 = match logic_eq_sym(state, th1) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th3 = match logic_beta_normalize_eq_full(state, th2) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_t = match logic_prop_truth_thm(state) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th3, th_t)
}

///|
pub fn logic_prop_imp_elim_thm(
  state : KernelState,
  prelude : PropPrelude,
  th_imp : Thm,
  th_p : Thm,
) -> Result[Thm, LogicError] {
  let imp_concl = match theorem_concl(th_imp) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let p_concl = match theorem_concl(th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (ante, cons) = match prop_dest_imp(state, prelude, imp_concl) {
    Some(v) => v
    None => return Err(logic_bool_type_mismatch())
  }
  if !term_logical_eq(ante, p_concl) {
    return Err(logic_bool_type_mismatch())
  }
  let th_imp_sym = match logic_eq_sym(state, th_imp) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_and = match logic_eq_mp_bool(state, th_imp_sym, th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q = match logic_prop_and_elim_r_thm(state, prelude, th_and) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let q_concl = match theorem_concl(th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_logical_eq(q_concl, cons) {
    return Err(logic_bool_type_mismatch())
  }
  Ok(th_q)
}

///|
pub fn logic_prop_imp_refl(
  state : KernelState,
  prelude : PropPrelude,
  p : Term,
) -> Result[Thm, LogicError] {
  let th_p = match logic_assume(state, p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_and = match logic_prop_and_intro_thm(state, prelude, th_p, th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let and_pp = match prop_mk_and(state, prelude, p, p) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th_assume_and = match logic_assume(state, and_pp) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_elim = match logic_prop_and_elim_l_thm(state, prelude, th_assume_and) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_deduct_antisym(state, th_and, th_elim)
}

///|
pub fn logic_prop_not_elim(
  state : KernelState,
  prelude : PropPrelude,
  th_not_p : Thm,
  th_p : Thm,
) -> Result[Thm, LogicError] {
  let not_concl = match theorem_concl(th_not_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let p_concl = match theorem_concl(th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let inner = match prop_dest_not(state, prelude, not_concl) {
    Some(v) => v
    None => return Err(logic_bool_type_mismatch())
  }
  if !term_logical_eq(inner, p_concl) {
    return Err(logic_bool_type_mismatch())
  }
  logic_prop_imp_elim_thm(state, prelude, th_not_p, th_p)
}

///|
pub fn logic_prop_imp_intro_thm(
  state : KernelState,
  prelude : PropPrelude,
  antecedent : Term,
  th_body : Thm,
) -> Result[Thm, LogicError] {
  let body_concl = match theorem_concl(th_body) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let has_hyp = match theorem_has_hyp(th_body, antecedent) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !has_hyp {
    return Err(logic_bool_type_mismatch())
  }
  let th_p = match logic_assume(state, antecedent) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_and = match logic_prop_and_intro_thm(state, prelude, th_p, th_body) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let and_term = match prop_mk_and(state, prelude, antecedent, body_concl) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th_assume_and = match logic_assume(state, and_term) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_left = match logic_prop_and_elim_l_thm(state, prelude, th_assume_and) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eq0 = match logic_deduct_antisym(state, th_and, th_left) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eq = match logic_normalize_prop_beta(state, th_eq0) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let target = match prop_mk_imp(state, prelude, antecedent, body_concl) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let concl = match theorem_concl(th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if term_logical_eq(concl, target) {
    Ok(th_eq)
  } else {
    Err(logic_bool_type_mismatch())
  }
}

///|
fn prop_logical_or_same(
  state : KernelState,
  prelude : PropPrelude,
  t1 : Term,
  t2 : Term,
) -> Bool {
  if term_logical_eq(t1, t2) || term_alpha_eq(t1, t2) {
    true
  } else {
    match (prop_dest_or(state, prelude, t1), prop_dest_or(state, prelude, t2)) {
      (Some((l1, r1)), Some((l2, r2))) =>
        (term_logical_eq(l1, l2) || term_alpha_eq(l1, l2)) &&
        (term_logical_eq(r1, r2) || term_alpha_eq(r1, r2))
      _ => false
    }
  }
}

///|
pub fn logic_prop_or_intro_l_thm(
  state : KernelState,
  prelude : PropPrelude,
  th_p : Thm,
  q : Term,
) -> Result[Thm, LogicError] {
  let p = match theorem_concl(th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let not_p = match prop_mk_not(state, prelude, p) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th_not_p = match logic_assume(state, not_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_false = match logic_prop_not_elim(state, prelude, th_not_p, th_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q = match theorem_ex_falso(state, prelude, th_false, q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let q_concl = match theorem_concl(th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_cur = match logic_prop_imp_intro_thm(state, prelude, not_p, th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let p_or_q = match prop_mk_or(state, prelude, p, q_concl) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let c = match theorem_concl(th_cur) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if prop_logical_or_same(state, prelude, c, p_or_q) {
    Ok(th_cur)
  } else {
    Err(logic_bool_type_mismatch())
  }
}

///|
fn bool_term_compat(state : KernelState, lhs : Term, rhs : Term) -> Bool {
  if term_logical_eq(lhs, rhs) || term_alpha_eq(lhs, rhs) {
    return true
  }
  let lhs_nf = match logic_beta_nf_bool_term_deep(state, lhs) {
    Ok(v) => v
    Err(_) => lhs
  }
  let rhs_nf = match logic_beta_nf_bool_term_deep(state, rhs) {
    Ok(v) => v
    Err(_) => rhs
  }
  term_logical_eq(lhs_nf, rhs_nf) || term_alpha_eq(lhs_nf, rhs_nf)
}

///|
fn prelude_false_term(state : KernelState, prelude : PropPrelude) -> Term? {
  match ks_mk_const(state, prelude.false_name) {
    Ok(v) => Some(v)
    Err(_) => None
  }
}

///|
fn find_matching_term(
  state : KernelState,
  pool : Array[Term],
  target : Term,
) -> Term? {
  for item in pool {
    if bool_term_compat(state, item, target) {
      return Some(item)
    }
  }
  None
}

///|
fn find_not_elim_pair(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
) -> (Term, Term)? {
  for not_term in pool {
    match prop_dest_not(state, prelude, not_term) {
      Some(inner) =>
        match find_matching_term(state, pool, inner) {
          Some(pos_term) => return Some((not_term, pos_term))
          None => ()
        }
      None => ()
    }
  }
  None
}

///|
fn find_named_and_owner(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
  want_left : Bool,
  goal_concl : Term,
) -> Term? {
  for owner in pool {
    match prop_dest_and(state, prelude, owner) {
      Some((lhs, rhs)) =>
        if want_left {
          if bool_term_compat(state, lhs, goal_concl) {
            return Some(owner)
          }
        } else if bool_term_compat(state, rhs, goal_concl) {
          return Some(owner)
        }
      _ => ()
    }
  }
  None
}

///|
pub fn logic_prop_named_theorem(
  state : KernelState,
  prelude : PropPrelude,
  name : String,
  goal_concl : Term,
) -> Thm? {
  if name == "imp_refl" {
    match prop_dest_imp(state, prelude, goal_concl) {
      Some((lhs, rhs)) =>
        if bool_term_compat(state, lhs, rhs) {
          match logic_prop_imp_refl(state, prelude, lhs) {
            Ok(th) => Some(th)
            Err(_) => None
          }
        } else {
          None
        }
      None => None
    }
  } else if name == "truth" {
    match prelude_false_term(state, prelude) {
      Some(_f) =>
        match ks_mk_const(state, prelude.truth_name) {
          Ok(t_term) =>
            if bool_term_compat(state, goal_concl, t_term) {
              match logic_prop_truth_const_thm(state, prelude) {
                Ok(th) => Some(th)
                Err(_) => None
              }
            } else {
              None
            }
          Err(_) => None
        }
      None => None
    }
  } else {
    None
  }
}

///|
pub fn logic_prop_context_theorem(
  state : KernelState,
  prelude : PropPrelude,
  name : String,
  pool : Array[Term],
  goal_concl : Term,
) -> (Thm, Term)? {
  if name == "and_elim_l" || name == "and_elim_r" {
    let want_left = name == "and_elim_l"
    match find_named_and_owner(state, prelude, pool, want_left, goal_concl) {
      Some(owner) => {
        let th_owner = match logic_assume(state, owner) {
          Ok(v) => v
          Err(_) => return None
        }
        let th_body = if want_left {
          match logic_prop_and_elim_l_thm(state, prelude, th_owner) {
            Ok(v) => v
            Err(_) => return None
          }
        } else {
          match logic_prop_and_elim_r_thm(state, prelude, th_owner) {
            Ok(v) => v
            Err(_) => return None
          }
        }
        Some((th_body, owner))
      }
      None => None
    }
  } else if name == "not_elim" {
    match prelude_false_term(state, prelude) {
      Some(false_term) =>
        if !bool_term_compat(state, goal_concl, false_term) {
          None
        } else {
          match find_not_elim_pair(state, prelude, pool) {
            Some((not_term, pos_term)) => {
              let th_not = match logic_assume(state, not_term) {
                Ok(v) => v
                Err(_) => return None
              }
              let th_pos = match logic_assume(state, pos_term) {
                Ok(v) => v
                Err(_) => return None
              }
              match logic_prop_not_elim(state, prelude, th_not, th_pos) {
                Ok(th) => {
                  let th_nf = match logic_normalize_prop_beta(state, th) {
                    Ok(v) => v
                    Err(_) => th
                  }
                  let direct = match thm_concl(th_nf) {
                    Ok(concl) =>
                      if bool_term_compat(state, concl, false_term) {
                        th_nf
                      } else {
                        let def_f = match
                          logic_bool_false_def_thm(state, prelude) {
                          Ok(v) => v
                          Err(_) => return None
                        }
                        let def_sym = match logic_eq_sym(state, def_f) {
                          Ok(v) => v
                          Err(_) => return None
                        }
                        match logic_eq_mp_bool(state, def_sym, th_nf) {
                          Ok(v) => v
                          Err(_) => return None
                        }
                      }
                    Err(_) => return None
                  }
                  Some((direct, false_term))
                }
                Err(_) => None
              }
            }
            None => None
          }
        }
      None => None
    }
  } else if name == "ex_falso" {
    match prelude_false_term(state, prelude) {
      Some(false_term) =>
        match find_matching_term(state, pool, false_term) {
          Some(found_false) => {
            let th_false = match logic_assume(state, found_false) {
              Ok(v) => v
              Err(_) => return None
            }
            match
              logic_prop_ex_falso_thm(state, prelude, th_false, goal_concl) {
              Ok(th) => {
                let th_nf = match logic_normalize_prop_beta(state, th) {
                  Ok(v) => v
                  Err(_) => th
                }
                Some((th_nf, found_false))
              }
              Err(_) => None
            }
          }
          None => None
        }
      None => None
    }
  } else {
    None
  }
}

///|
pub fn logic_prop_context_apply_theorem(
  state : KernelState,
  prelude : PropPrelude,
  name : String,
  pool : Array[Term],
  goal_concl : Term,
) -> (Thm, Term)? {
  if name == "and_elim_l" || name == "and_elim_r" {
    let want_left = name == "and_elim_l"
    match find_named_and_owner(state, prelude, pool, want_left, goal_concl) {
      Some(owner) => {
        let th_owner = match logic_assume(state, owner) {
          Ok(v) => v
          Err(_) => return None
        }
        let th_body = if want_left {
          match logic_prop_and_elim_l_thm(state, prelude, th_owner) {
            Ok(v) => v
            Err(_) => return None
          }
        } else {
          match logic_prop_and_elim_r_thm(state, prelude, th_owner) {
            Ok(v) => v
            Err(_) => return None
          }
        }
        match logic_prop_imp_intro_thm(state, prelude, owner, th_body) {
          Ok(th) => Some((th, owner))
          Err(_) => None
        }
      }
      None => None
    }
  } else if name == "or_intro_l" {
    match prop_dest_or(state, prelude, goal_concl) {
      Some((lhs, rhs)) => {
        let th_lhs = match logic_assume(state, lhs) {
          Ok(v) => v
          Err(_) => return None
        }
        let th_body = match
          logic_prop_or_intro_l_thm(state, prelude, th_lhs, rhs) {
          Ok(v) => v
          Err(_) => return None
        }
        match logic_prop_imp_intro_thm(state, prelude, lhs, th_body) {
          Ok(th) => Some((th, lhs))
          Err(_) => None
        }
      }
      None => None
    }
  } else if name == "or_intro_r" {
    match prop_dest_or(state, prelude, goal_concl) {
      Some((lhs, rhs)) => {
        let th_rhs = match logic_assume(state, rhs) {
          Ok(v) => v
          Err(_) => return None
        }
        let th_body = match
          logic_prop_or_intro_r_thm(state, prelude, lhs, th_rhs) {
          Ok(v) => v
          Err(_) => return None
        }
        match logic_prop_imp_intro_thm(state, prelude, rhs, th_body) {
          Ok(th) => Some((th, rhs))
          Err(_) => None
        }
      }
      None => None
    }
  } else {
    None
  }
}

///|
pub fn logic_prop_or_intro_r_thm(
  state : KernelState,
  prelude : PropPrelude,
  p : Term,
  th_q : Thm,
) -> Result[Thm, LogicError] {
  let q = match theorem_concl(th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let not_p = match prop_mk_not(state, prelude, p) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let th_not_p = match logic_assume(state, not_p) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q_with_h = match
    logic_prop_and_intro_thm(state, prelude, th_not_p, th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q_only = match logic_prop_and_elim_r_thm(state, prelude, th_q_with_h) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_cur = match
    logic_prop_imp_intro_thm(state, prelude, not_p, th_q_only) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let p_or_q = match prop_mk_or(state, prelude, p, q) {
    Ok(v) => v
    Err(_) => return Err(logic_bool_type_mismatch())
  }
  let c = match theorem_concl(th_cur) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if prop_logical_or_same(state, prelude, c, p_or_q) {
    Ok(th_cur)
  } else {
    Err(logic_bool_type_mismatch())
  }
}
