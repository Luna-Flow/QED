///|
pub fn logic_prop_assume(
  state : KernelState,
  goal_term : Term,
) -> Result[Thm, LogicError] {
  logic_assume(state, goal_term)
}

///|
fn replay_logic_err() -> LogicError {
  match mk_eq(mk_var("_rp_a", bool_ty()), mk_var("_rp_b", mk_tyvar("_RP"))) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
pub fn logic_prop_strengthen_to_hyps(
  state : KernelState,
  target_hyps : Array[Term],
  th : Thm,
) -> Result[Thm, LogicError] {
  let mut t = th
  for h in target_hyps {
    let hs = match thm_hyps(t) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
    if !hs.any(fn(x) { term_logical_eq(x, h) }) {
      t = match logic_add_assum(state, h, t) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
    }
  }
  let hs2 = match thm_hyps(t) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  for x in hs2 {
    if !target_hyps.any(fn(h) { term_logical_eq(h, x) }) {
      return Err(replay_logic_err())
    }
  }
  for h in target_hyps {
    if !hs2.any(fn(x) { term_logical_eq(x, h) }) {
      return Err(replay_logic_err())
    }
  }
  Ok(t)
}

///|
pub fn logic_prop_close_hypothesis(
  state : KernelState,
  hyps : Array[Term],
  concl : Term,
) -> Result[Thm, LogicError] {
  let th0 = match logic_assume(state, concl) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_prop_strengthen_to_hyps(state, hyps, th0)
}

///|
pub fn logic_prop_ensure_sequent(
  state : KernelState,
  hyps : Array[Term],
  concl : Term,
  th : Thm,
) -> Result[Thm, LogicError] {
  let c = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !(term_logical_eq(c, concl) || term_alpha_eq(c, concl)) {
    return Err(replay_logic_err())
  }
  logic_prop_strengthen_to_hyps(state, hyps, th)
}

///|
pub fn logic_prop_discharge_imp_prefix(
  state : KernelState,
  prelude : PropPrelude,
  prefix : Array[Term],
  th : Thm,
) -> Result[Thm, LogicError] {
  let mut t = th
  let mut i = prefix.length()
  while i > 0 {
    i = i - 1
    let a = prefix[i]
    t = match logic_prop_imp_intro_thm(state, prelude, a, t) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
  }
  Ok(t)
}

///|
pub fn logic_prop_replay_imp_elim_backward(
  state : KernelState,
  prelude : PropPrelude,
  hyps : Array[Term],
  imp_term : Term,
  th_antecedent : Thm,
) -> Result[Thm, LogicError] {
  let (a, _b) = match prop_dest_imp(state, prelude, imp_term) {
    Some(v) => v
    None => return Err(replay_logic_err())
  }
  let th_sub = match logic_prop_ensure_sequent(state, hyps, a, th_antecedent) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_i0 = match logic_assume(state, imp_term) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_i = match logic_prop_strengthen_to_hyps(state, hyps, th_i0) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_prop_imp_elim_thm(state, prelude, th_i, th_sub)
}

///|
pub fn logic_prop_replay_imp_elim_backward_thm(
  state : KernelState,
  prelude : PropPrelude,
  hyps : Array[Term],
  imp_th : Thm,
  th_antecedent : Thm,
) -> Result[Thm, LogicError] {
  let imp_concl = match thm_concl(imp_th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let (antecedent, _consequent) = match
    prop_dest_imp(state, prelude, imp_concl) {
    Some(v) => v
    None => return Err(replay_logic_err())
  }
  let th_imp = match logic_prop_ensure_sequent(state, hyps, imp_concl, imp_th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let th_sub = match
    logic_prop_ensure_sequent(state, hyps, antecedent, th_antecedent) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  logic_prop_imp_elim_thm(state, prelude, th_imp, th_sub)
}

///|
pub fn logic_prop_replay_and_elim_l(
  state : KernelState,
  prelude : PropPrelude,
  expected : Term,
  th_and : Thm,
) -> Result[Thm, LogicError] {
  let th = match logic_prop_and_elim_l_thm(state, prelude, th_and) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let c = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_logical_eq(c, expected) {
    Err(replay_logic_err())
  } else {
    Ok(th)
  }
}

///|
pub fn logic_prop_replay_and_elim_r(
  state : KernelState,
  prelude : PropPrelude,
  expected : Term,
  th_and : Thm,
) -> Result[Thm, LogicError] {
  let th = match logic_prop_and_elim_r_thm(state, prelude, th_and) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let c = match thm_concl(th) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_logical_eq(c, expected) {
    Err(replay_logic_err())
  } else {
    Ok(th)
  }
}

///|
pub fn logic_prop_merge_conjunction(
  state : KernelState,
  prelude : PropPrelude,
  th_a : Thm,
  th_b : Thm,
  and_term : Term,
) -> Result[Thm, LogicError] {
  let thm = match logic_prop_and_intro_thm(state, prelude, th_a, th_b) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let c = match thm_concl(thm) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  if !term_logical_eq(c, and_term) {
    Err(replay_logic_err())
  } else {
    Ok(thm)
  }
}

///|
pub fn logic_prop_or_wrap_left(
  state : KernelState,
  prelude : PropPrelude,
  _full_or : Term,
  right_branch : Term,
  th_left_branch : Thm,
) -> Result[Thm, LogicError] {
  logic_prop_or_intro_l_thm(state, prelude, th_left_branch, right_branch)
}

///|
pub fn logic_prop_or_wrap_right(
  state : KernelState,
  prelude : PropPrelude,
  _full_or : Term,
  left_branch : Term,
  th_right_branch : Thm,
) -> Result[Thm, LogicError] {
  logic_prop_or_intro_r_thm(state, prelude, left_branch, th_right_branch)
}
