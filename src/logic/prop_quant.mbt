// Quantifiers as unfolded definitions over the prelude.
//
// `∀x. φ` is `(λx. φ) = (λx. T)` with `T` the prelude truth constant, the shape
// the tactics layer introduces for quantified goals (HOL Light `!`, unfolded).
// `∃x. φ` is `∀q. (∀x. φ ⇒ q) ⇒ q` for a boolean `q` not free in `φ`; this
// needs no choice, unlike HOL Light's `?P = P (@P)`. The four rules follow Lean
// `Derivation.allIntro`, `allElim`, `exIntro` and `exElim`, and are derived from
// the kernel rules, so they add no authority.

///|
fn quant_var_free_in_hyp() -> LogicError {
  let p = mk_var("_q_free", bool_ty())
  let st = empty_kernel_state()
  let th = match assume_checked(st, p) {
    Ok(v) => v
    Err(_) => panic()
  }
  match abs_rule_checked(st, p, th) {
    Ok(_) => panic()
    Err(e) => e
  }
}

///|
fn quant_var_name(x : Term) -> String? {
  match free_vars(x) {
    [(name, _)] =>
      if term_alpha_eq(mk_var(name, type_of(x).unwrap()), x) {
        Some(name)
      } else {
        None
      }
    _ => None
  }
}

///|
fn quant_has_free(terms : Array[Term], name : String, ty : HolType) -> Bool {
  terms.any(fn(t) { free_vars(t).any(fn(v) { v.0 == name && ty_eq(v.1, ty) }) })
}

///|
fn quant_truth_const(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Term, LogicError] {
  match ks_definition_theorem(state, prelude.truth_name) {
    Ok(th) => logic_prop_def_lhs(th)
    Err(_) => Err(logic_bool_type_mismatch())
  }
}

///|
/// `∀x. body` for a variable `x` and a boolean `body`.
pub fn logic_quant_mk_all(
  state : KernelState,
  prelude : PropPrelude,
  x : Term,
  body : Term,
) -> Result[Term, LogicError] {
  if quant_var_name(x) is None {
    return Err(logic_bool_type_mismatch())
  }
  match require_bool_term(body) {
    Ok(_) => ()
    Err(e) => return Err(e)
  }
  let t = match quant_truth_const(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  mk_eq(mk_abs(x, body), mk_abs(x, t))
}

///|
/// The binder and body of `∀x. body`.
pub fn logic_quant_dest_all(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> (Term, Term)? {
  let t = match quant_truth_const(state, prelude) {
    Ok(v) => v
    Err(_) => return None
  }
  let (lhs, rhs) = match dest_eq(term) {
    Ok(v) => v
    Err(_) => return None
  }
  match (dest_abs(lhs), dest_abs(rhs)) {
    (Some((x, body)), Some((_, rhs_body))) =>
      if term_alpha_eq(rhs_body, t) &&
        type_of(body).map(fn(ty) { ty_eq(ty, bool_ty()) }).unwrap_or(false) {
        Some((x, body))
      } else {
        None
      }
    _ => None
  }
}

///|
fn quant_ex_bound(x : Term, body : Term) -> Term {
  mk_var(fresh_binder_name("_q_ex", [x, body]), bool_ty())
}

///|
/// `∃x. body`, that is `∀q. (∀x. body ⇒ q) ⇒ q`.
pub fn logic_quant_mk_ex(
  state : KernelState,
  prelude : PropPrelude,
  x : Term,
  body : Term,
) -> Result[Term, LogicError] {
  let q = quant_ex_bound(x, body)
  let inner = match prop_mk_imp(state, prelude, body, q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let all_inner = match logic_quant_mk_all(state, prelude, x, inner) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let outer = match prop_mk_imp(state, prelude, all_inner, q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_quant_mk_all(state, prelude, q, outer)
}

///|
/// The binder and body of `∃x. body`.
pub fn logic_quant_dest_ex(
  state : KernelState,
  prelude : PropPrelude,
  term : Term,
) -> (Term, Term)? {
  let (q, outer) = match logic_quant_dest_all(state, prelude, term) {
    Some(v) => v
    None => return None
  }
  let (all_inner, q1) = match prop_dest_imp(state, prelude, outer) {
    Some(v) => v
    None => return None
  }
  let (x, inner) = match logic_quant_dest_all(state, prelude, all_inner) {
    Some(v) => v
    None => return None
  }
  let (body, q2) = match prop_dest_imp(state, prelude, inner) {
    Some(v) => v
    None => return None
  }
  let q_name = match quant_var_name(q) {
    Some(v) => v
    None => return None
  }
  if term_alpha_eq(q1, q) &&
    term_alpha_eq(q2, q) &&
    !quant_has_free([x, body], q_name, bool_ty()) {
    Some((x, body))
  } else {
    None
  }
}

///|
/// Lean `Derivation.allIntro`, HOL Light `GEN`: from `Γ ⊢ φ` with `x` not free
/// in `Γ`, derive `Γ ⊢ ∀x. φ`.
pub fn logic_quant_all_intro_thm(
  state : KernelState,
  prelude : PropPrelude,
  x : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  let body = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let target = match logic_quant_mk_all(state, prelude, x, body) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let t = match quant_truth_const(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  // `Γ ⊢ φ = T` drops a hypothesis `T`; it is added back so the hypotheses are
  // exactly those of the premise.
  let had_truth = match theorem_has_hyp(th, t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eq = match theorem_eq_to_truth(state, prelude, th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_eq = if had_truth {
    match logic_add_assum(state, t, th_eq) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
  } else {
    th_eq
  }
  let th_all = match logic_abs_rule(state, x, th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  match thm_concl(th_all) {
    Ok(c) if term_alpha_eq(c, target) => Ok(th_all)
    Ok(_) => Err(logic_bool_type_mismatch())
    Err(e) => Err(e)
  }
}

///|
/// Lean `Derivation.allElim`, HOL Light `SPEC`: from `Γ ⊢ ∀x. φ` derive
/// `Γ ⊢ φ[t/x]`. Only the outer redex is reduced.
pub fn logic_quant_all_elim_thm(
  state : KernelState,
  prelude : PropPrelude,
  t : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  let concl = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (lhs, rhs) = match logic_quant_dest_all(state, prelude, concl) {
    Some(_) =>
      match dest_eq(concl) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
    None => return Err(logic_bool_type_mismatch())
  }
  let th_app = match logic_apply_fun_eq(state, th, t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_beta_l = match logic_beta_rule(state, mk_comb(lhs, t)) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_beta_r = match logic_beta_rule(state, mk_comb(rhs, t)) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_l = match logic_eq_sym(state, th_beta_l) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_mid = match logic_trans(state, th_app, th_beta_r) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  // `Γ ⊢ φ[t/x] = T`
  let th_eq = match logic_trans(state, th_l, th_mid) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_sym = match logic_eq_sym(state, th_eq) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_t = match logic_prop_truth_const_thm(state, prelude) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_sym, th_t)
}

///|
/// Lean `Derivation.exIntro`, HOL Light `EXISTS`: from `Γ ⊢ φ[t/x]` derive
/// `Γ ⊢ ∃x. φ`.
pub fn logic_quant_ex_intro_thm(
  state : KernelState,
  prelude : PropPrelude,
  x : Term,
  body : Term,
  t : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  let target = match logic_quant_mk_ex(state, prelude, x, body) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let hyps = match thm_hyps(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  // `q` must also be fresh for the hypotheses, so that it can be generalised.
  let q = mk_var(fresh_binder_name("_q_ex", [x, body, t, ..hyps]), bool_ty())
  let inner = match prop_mk_imp(state, prelude, body, q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let all_inner = match logic_quant_mk_all(state, prelude, x, inner) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_h = match logic_assume(state, all_inner) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_imp = match logic_quant_all_elim_thm(state, prelude, t, th_h) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_q = match logic_prop_imp_elim_thm(state, prelude, th_imp, th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_outer = match
    logic_prop_imp_intro_thm(state, prelude, all_inner, th_q) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_ex = match logic_quant_all_intro_thm(state, prelude, q, th_outer) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  // If a hypothesis of the premise is `∀x. φ ⇒ q` itself, `imp_intro`
  // discharged it; that cannot happen because `q` is fresh for the hypotheses.
  match thm_concl(th_ex) {
    Ok(c) if term_alpha_eq(c, target) => Ok(th_ex)
    Ok(_) => Err(logic_bool_type_mismatch())
    Err(e) => Err(e)
  }
}

///|
/// Lean `Derivation.exElim`, HOL Light `CHOOSE`: from `A ⊢ ∃x. φ` and
/// `Δ ∪ {φ[v/x]} ⊢ B`, with `v` a variable not free in `∃x. φ`, `B` or `Δ`,
/// derive `A ∪ Δ ⊢ B`.
pub fn logic_quant_ex_elim_thm(
  state : KernelState,
  prelude : PropPrelude,
  th_ex : Thm,
  v : Term,
  th_b : Thm,
) -> Result[Thm, LogicError] {
  let ex_concl = match thm_concl(th_ex) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (x, body) = match logic_quant_dest_ex(state, prelude, ex_concl) {
    Some(v) => v
    None => return Err(logic_bool_type_mismatch())
  }
  let v_name = match quant_var_name(v) {
    Some(n) => n
    None => return Err(logic_bool_type_mismatch())
  }
  let v_ty = type_of(v).unwrap()
  match type_of(x) {
    Some(x_ty) if ty_eq(x_ty, v_ty) => ()
    _ => return Err(logic_bool_type_mismatch())
  }
  let b = match thm_concl(th_b) {
    Ok(c) => c
    Err(e) => return Err(e)
  }
  let body_v = match logic_beta_rule(state, mk_comb(mk_abs(x, body), v)) {
    Ok(th) =>
      match logic_prop_def_rhs(th) {
        Ok(c) => c
        Err(e) => return Err(e)
      }
    Err(e) => return Err(e)
  }
  let delta = match thm_hyps(th_b) {
    Ok(hs) => hs.filter(fn(h) { !term_logical_eq(h, body_v) })
    Err(e) => return Err(e)
  }
  if quant_has_free([ex_concl, b, ..delta], v_name, v_ty) {
    return Err(quant_var_free_in_hyp())
  }
  let th_imp = match logic_prop_imp_intro_thm(state, prelude, body_v, th_b) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_all = match logic_quant_all_intro_thm(state, prelude, v, th_imp) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_spec = match logic_quant_all_elim_thm(state, prelude, b, th_ex) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_prop_imp_elim_thm(state, prelude, th_spec, th_all)
}
