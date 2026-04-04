///|
pub fn logic_prop_truth_term() -> Term {
  let x = mk_var("_p_true", bool_ty())
  let id = mk_abs(x, x)
  match mk_eq(id, id) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
pub fn logic_prop_false_term() -> Term {
  let p = mk_var("_p_false", bool_ty())
  let pred = mk_abs(p, p)
  match
    mk_eq(
      pred,
      mk_abs(mk_var("_p_truth_fn", bool_ty()), logic_prop_truth_term()),
    ) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
fn logic_foundation_type_mismatch() -> LogicError {
  match
    mk_eq(mk_var("_lf_tm_a", bool_ty()), mk_var("_lf_tm_b", mk_tyvar("_LF"))) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn logic_foundation_alpha_mismatch() -> LogicError {
  let p = mk_var("_lf_p", bool_ty())
  let q = mk_var("_lf_q", bool_ty())
  let r = mk_var("_lf_r", bool_ty())
  let th_eq = match logic_assume(empty_kernel_state(), expect_prop_eq(p, q)) {
    Ok(v) => v
    Err(_) => panic()
  }
  let th_r = match logic_assume(empty_kernel_state(), r) {
    Ok(v) => v
    Err(_) => panic()
  }
  match logic_eq_mp(empty_kernel_state(), th_eq, th_r) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn expect_prop_eq(lhs : Term, rhs : Term) -> Term {
  match mk_eq(lhs, rhs) {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
pub fn logic_prop_def_imp(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, SigError] {
  ks_definition_theorem(state, prelude.imp_name)
}

///|
pub fn logic_prop_def_not(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, SigError] {
  ks_definition_theorem(state, prelude.not_name)
}

///|
pub fn logic_prop_def_and(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, SigError] {
  ks_definition_theorem(state, prelude.and_name)
}

///|
pub fn logic_prop_def_or(
  state : KernelState,
  prelude : PropPrelude,
) -> Result[Thm, SigError] {
  ks_definition_theorem(state, prelude.or_name)
}

///|
pub fn logic_prop_def_lhs(th : Thm) -> Result[Term, LogicError] {
  match thm_concl(th) {
    Ok(concl) =>
      match dest_eq(concl) {
        Ok((lhs, _)) => Ok(lhs)
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
pub fn logic_prop_def_rhs(th : Thm) -> Result[Term, LogicError] {
  match thm_concl(th) {
    Ok(concl) =>
      match dest_eq(concl) {
        Ok((_, rhs)) => Ok(rhs)
        Err(e) => Err(e)
      }
    Err(e) => Err(e)
  }
}

///|
fn term_eq_thm_lhs(th : Thm) -> Result[Term, LogicError] {
  logic_prop_def_lhs(th)
}

///|
fn dest_app_spine(term : Term) -> (Term, Array[Term]) {
  let args : Array[Term] = []
  let mut head = term
  while true {
    match dest_comb(head) {
      Some((f, x)) => {
        args.push(x)
        head = f
      }
      None => break
    }
  }
  let out : Array[Term] = []
  let mut i = args.length()
  while i > 0 {
    i = i - 1
    out.push(args[i])
  }
  (head, out)
}

///|
pub fn logic_prop_unfold_head(
  state : KernelState,
  th_def : Thm,
  th_term : Thm,
) -> Result[Thm, LogicError] {
  let def_lhs = match term_eq_thm_lhs(th_def) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let term_concl = match thm_concl(th_term) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (head, args) = dest_app_spine(term_concl)
  if !term_logical_eq(head, def_lhs) {
    return Err(logic_foundation_alpha_mismatch())
  }
  let th_applied = match args.length() {
    0 => th_def
    1 =>
      match logic_apply_fun_eq(state, th_def, args[0]) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
    2 =>
      match logic_apply_fun_eq2(state, th_def, args[0], args[1]) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
    _ => return Err(logic_foundation_type_mismatch())
  }
  let th_norm = match logic_beta_normalize_eq(state, th_applied) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_eq_mp_bool(state, th_norm, th_term)
}

///|
pub fn logic_prop_unfold_imp(
  state : KernelState,
  prelude : PropPrelude,
  th_imp_term : Thm,
) -> Result[Thm, LogicError] {
  match logic_prop_def_imp(state, prelude) {
    Ok(def_th) => logic_prop_unfold_head(state, def_th, th_imp_term)
    Err(_) => Err(logic_foundation_type_mismatch())
  }
}

///|
pub fn logic_prop_unfold_and(
  state : KernelState,
  prelude : PropPrelude,
  th_and_term : Thm,
) -> Result[Thm, LogicError] {
  match logic_prop_def_and(state, prelude) {
    Ok(def_th) => logic_prop_unfold_head(state, def_th, th_and_term)
    Err(_) => Err(logic_foundation_type_mismatch())
  }
}

///|
pub fn logic_prop_unfold_or(
  state : KernelState,
  prelude : PropPrelude,
  th_or_term : Thm,
) -> Result[Thm, LogicError] {
  match logic_prop_def_or(state, prelude) {
    Ok(def_th) => logic_prop_unfold_head(state, def_th, th_or_term)
    Err(_) => Err(logic_foundation_type_mismatch())
  }
}

///|
pub fn logic_prop_unfold_not(
  state : KernelState,
  prelude : PropPrelude,
  th_not_term : Thm,
) -> Result[Thm, LogicError] {
  match logic_prop_def_not(state, prelude) {
    Ok(def_th) => logic_prop_unfold_head(state, def_th, th_not_term)
    Err(_) => Err(logic_foundation_type_mismatch())
  }
}
