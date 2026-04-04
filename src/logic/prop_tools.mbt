///|
fn logic_tools_type_mismatch() -> LogicError {
  match mk_eq(mk_var("_lt_a", bool_ty()), mk_var("_lt_b", mk_tyvar("_LT"))) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
pub fn logic_prop_truth_thm(state : KernelState) -> Result[Thm, LogicError] {
  let x = mk_var("_p_true", bool_ty())
  let id = mk_abs(x, x)
  logic_refl(state, id)
}

///|
/// HOL-Light `TRUTH`: proves `⊢ T` for the prelude truth constant
/// (`T = (λx.x) = (λx.x)` in the shallow encoding).
pub fn logic_prop_truth_const_thm(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, LogicError] {
  let th_def = match ks_definition_theorem(state, prelude.truth_name) {
    Ok(v) => v
    Err(_) => return Err(logic_tools_type_mismatch())
  }
  let th_sym = match logic_eq_sym(state, th_def) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let x = mk_var("_p_true", bool_ty())
  let id = mk_abs(x, x)
  let th_refl_core = match logic_refl(state, id) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_sym, th_refl_core)
}

///|
pub fn logic_eq_mp_bool(
  state : KernelState,
  th_eq : Thm,
  th_bool : Thm,
) -> Result[Thm, LogicError] {
  let concl = match thm_concl(th_bool) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match type_of(concl) {
    Some(ty) =>
      if ty_eq(ty, bool_ty()) {
        logic_eq_mp(state, th_eq, th_bool)
      } else {
        Err(logic_tools_type_mismatch())
      }
    None => Err(logic_tools_type_mismatch())
  }
}

///|
pub fn logic_apply_fun_eq(
  state : KernelState,
  th_eq_fun : Thm,
  arg : Term,
) -> Result[Thm, LogicError] {
  let th_arg = match logic_refl(state, arg) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_mk_comb_rule(state, th_eq_fun, th_arg)
}

///|
pub fn logic_apply_fun_eq2(
  state : KernelState,
  th_eq_fun : Thm,
  arg1 : Term,
  arg2 : Term,
) -> Result[Thm, LogicError] {
  let th1 = match logic_apply_fun_eq(state, th_eq_fun, arg1) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_apply_fun_eq(state, th1, arg2)
}

///|
/// Leftmost-outermost β-step on a subterm of `t`, yielding `⊢ t = t'` when some redex exists.
fn logic_beta_redex_at(
  state : KernelState,
  t : Term,
) -> Result[Thm, LogicError] {
  match logic_beta_rule(state, t) {
    Ok(th) => return Ok(th)
    Err(NotTrivialBetaRedex) => ()
    Err(e) => return Err(e)
  }
  match dest_comb(t) {
    Some((f, x)) =>
      match logic_beta_redex_at(state, f) {
        Ok(th_fun) => {
          let th_x = match logic_refl(state, x) {
            Ok(v) => v
            Err(e) => return Err(e)
          }
          logic_mk_comb_rule(state, th_fun, th_x)
        }
        Err(NotTrivialBetaRedex) =>
          match logic_beta_redex_at(state, x) {
            Ok(th_x) => {
              let th_f = match logic_refl(state, f) {
                Ok(v) => v
                Err(e) => return Err(e)
              }
              logic_mk_comb_rule(state, th_f, th_x)
            }
            Err(e) => Err(e)
          }
        Err(e) => Err(e)
      }
    None =>
      match logic_beta_rule(state, t) {
        Err(e) => Err(e)
        Ok(_) => panic()
      }
  }
}

///|
/// Normalize the RHS of `th_eq` by repeated LO β (including inside `Comb` spines).
fn logic_beta_normalize_eq_full(
  state : KernelState,
  th_eq : Thm,
) -> Result[Thm, LogicError] {
  let mut cur = th_eq
  let mut steps = 0
  while steps < 512 {
    let rhs = match thm_concl(cur) {
      Ok(concl) =>
        match dest_eq(concl) {
          Ok((_, r)) => r
          Err(e) => return Err(e)
        }
      Err(e) => return Err(e)
    }
    match logic_beta_redex_at(state, rhs) {
      Ok(th_beta) => {
        cur = match logic_trans(state, cur, th_beta) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        steps = steps + 1
      }
      Err(NotTrivialBetaRedex) => return Ok(cur)
      Err(e) => return Err(e)
    }
  }
  Ok(cur)
}

///|
/// β-normal form of a bool proposition term (for replay/tactic QED checks). Uses `⊢ t = t`
/// and the same LO β engine as `logic_normalize_prop_beta`; returns `t` unchanged on failure.
pub fn logic_beta_nf_bool_term(
  state : KernelState,
  t : Term,
) -> Result[Term, LogicError] {
  let th0 = match logic_refl(state, t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th1 = match logic_beta_normalize_eq_full(state, th0) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let concl = match thm_concl(th1) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match dest_eq(concl) {
    Ok((_l, r)) => Ok(r)
    Err(_) => Ok(t)
  }
}

///|
/// Repeated `logic_beta_nf_bool_term` until fixpoint (bounded), for deeply nested prop encodings.
pub fn logic_beta_nf_bool_term_deep(
  state : KernelState,
  t : Term,
) -> Result[Term, LogicError] {
  let mut cur = t
  let mut steps = 0
  while steps < 32 {
    let next = match logic_beta_nf_bool_term(state, cur) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
    if term_logical_eq(cur, next) || term_alpha_eq(cur, next) {
      break
    }
    cur = next
    steps = steps + 1
  }
  Ok(cur)
}

///|
/// From `⊢ C` derive `⊢ C'` where `C'` β-reduces `C` inside `Comb` spines (same engine as
/// `logic_beta_normalize_eq_full` on `⊢ C = C`).
pub fn logic_normalize_prop_beta(
  state : KernelState,
  th : Thm,
) -> Result[Thm, LogicError] {
  let c = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_same = match logic_refl(state, c) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_bn = match logic_beta_normalize_eq_full(state, th_same) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_bn, th)
}

///|
fn beta_normalize_eq_go(
  state : KernelState,
  th_eq : Thm,
) -> Result[Thm, LogicError] {
  let rhs = match thm_concl(th_eq) {
    Ok(concl) =>
      match dest_eq(concl) {
        Ok((_, rhs)) => rhs
        Err(e) => return Err(e)
      }
    Err(e) => return Err(e)
  }
  match logic_beta_rule(state, rhs) {
    Ok(th_beta) => {
      let th2 = match logic_trans(state, th_eq, th_beta) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      beta_normalize_eq_go(state, th2)
    }
    Err(NotTrivialBetaRedex) => Ok(th_eq)
    Err(e) => Err(e)
  }
}

///|
pub fn logic_beta_normalize_eq(
  state : KernelState,
  th_eq : Thm,
) -> Result[Thm, LogicError] {
  beta_normalize_eq_go(state, th_eq)
}

///|
pub fn logic_eq_sym(
  state : KernelState,
  th_eq : Thm,
) -> Result[Thm, LogicError] {
  let concl = match thm_concl(th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (lhs, _) = match dest_eq(concl) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let lhs_ty = match type_of(lhs) {
    Some(v) => v
    None => return Err(logic_tools_type_mismatch())
  }
  let eq_const = mk_const("=", fun_ty(lhs_ty, fun_ty(lhs_ty, bool_ty())))
  let eq_refl = match logic_refl(state, eq_const) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let eq_lift = match logic_mk_comb_rule(state, eq_refl, th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_lhs = match logic_refl(state, lhs) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eqeq = match logic_mk_comb_rule(state, eq_lift, th_lhs) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_eqeq, th_lhs)
}
