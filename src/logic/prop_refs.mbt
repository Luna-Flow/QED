///|
pub enum PropRefResolution {
  LocalFact(Term)
  NamedTheorem(Thm)
  ContextDerived(Thm, Term)
}

///|
pub enum PropApplyTheoremResolution {
  Applicable(Thm, Term)
  KnownButUnavailable
}

///|
pub enum PropExactTheoremResolution {
  ExactApplicable(Thm)
  ExactKnownButUnavailable
}

///|
pub enum PropExactWitness {
  ExactLocalAlias(String)
  ExactDirectTheorem(String, Thm)
  ExactContextTheorem(String, Thm, Array[Term])
}

///|
pub enum PropExactWitnessResolution {
  ExactWitnessApplicable(PropExactWitness)
  ExactWitnessKnownButUnavailable
}

///|
fn resolve_local_fact(locals : Array[(String, Term)], name : String) -> Term? {
  let mut i = locals.length()
  while i > 0 {
    i = i - 1
    let (local_name, local_term) = locals[i]
    if local_name == name {
      return Some(local_term)
    }
  }
  None
}

///|
fn exact_local_alias_matches(
  hyps : Array[Term],
  concl : Term,
  term : Term,
) -> Bool {
  hyps.any(fn(h) {
    (term_logical_eq(h, concl) || term_alpha_eq(h, concl)) &&
    (term_logical_eq(term, h) || term_alpha_eq(term, h))
  })
}

///|
fn exact_context_supports(th : Thm) -> Array[Term]? {
  match thm_hyps(th) {
    Ok(hs) => Some(hs)
    Err(_) => None
  }
}

///|
fn exact_pool_from_locals(
  locals : Array[(String, Term)],
  hyps : Array[Term],
) -> Array[Term] {
  let out : Array[Term] = []
  for h in hyps {
    out.push(h)
  }
  for item in locals {
    let (_, term) = item
    out.push(term)
  }
  out
}

///|
/// Legacy mixed resolver retained for tests and non-tactic helpers.
/// `ProofState` and `prover` should use the mode-specific exact/apply resolvers.
pub fn logic_prop_resolve_ref(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  pool : Array[Term],
  goal_concl : Term,
  name : String,
) -> PropRefResolution? {
  match resolve_local_fact(locals, name) {
    Some(term) => return Some(LocalFact(term))
    None => ()
  }
  match logic_prop_theorem_entry(name) {
    Some(entry) =>
      match entry.exact_class {
        Some(DirectClose) =>
          match logic_prop_named_theorem(state, prelude, name, goal_concl) {
            Some(th) => Some(NamedTheorem(th))
            None => None
          }
        Some(ContextDerived) =>
          match
            logic_prop_context_theorem(state, prelude, name, pool, goal_concl) {
            Some((th, antecedent)) => Some(ContextDerived(th, antecedent))
            None => None
          }
        _ => None
      }
    None => None
  }
}

///|
/// Unified witness resolution for `exact`.
pub fn logic_prop_resolve_exact_witness(
  state : KernelState,
  prelude : PropPrelude,
  locals : Array[(String, Term)],
  hyps : Array[Term],
  goal_concl : Term,
  name : String,
) -> PropExactWitnessResolution? {
  match resolve_local_fact(locals, name) {
    Some(term) =>
      if exact_local_alias_matches(hyps, goal_concl, term) {
        return Some(ExactWitnessApplicable(ExactLocalAlias(name)))
      } else {
        return Some(ExactWitnessKnownButUnavailable)
      }
    None => ()
  }
  let pool = exact_pool_from_locals(locals, hyps)
  match logic_prop_theorem_entry(name) {
    Some(entry) =>
      match entry.exact_class {
        Some(DirectClose) =>
          match logic_prop_named_theorem(state, prelude, name, goal_concl) {
            Some(th) =>
              Some(ExactWitnessApplicable(ExactDirectTheorem(name, th)))
            None => Some(ExactWitnessKnownButUnavailable)
          }
        Some(ContextDerived) =>
          match
            logic_prop_context_theorem(state, prelude, name, pool, goal_concl) {
            Some((th, _)) =>
              match exact_context_supports(th) {
                Some(supports) =>
                  Some(
                    ExactWitnessApplicable(
                      ExactContextTheorem(name, th, supports),
                    ),
                  )
                None => Some(ExactWitnessKnownButUnavailable)
              }
            None => Some(ExactWitnessKnownButUnavailable)
          }
        _ => Some(ExactWitnessKnownButUnavailable)
      }
    None => None
  }
}

///|
/// Mode-specific theorem resolution for `exact`.
/// This theorem-only helper is retained for callers that do not model local
/// hypothesis witnesses explicitly.
pub fn logic_prop_resolve_exact_theorem(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
  goal_concl : Term,
  name : String,
) -> PropExactTheoremResolution? {
  match logic_prop_theorem_entry(name) {
    Some(entry) =>
      match entry.exact_class {
        Some(DirectClose) =>
          match logic_prop_named_theorem(state, prelude, name, goal_concl) {
            Some(th) => Some(ExactApplicable(th))
            None => Some(ExactKnownButUnavailable)
          }
        Some(ContextDerived) =>
          match
            logic_prop_context_theorem(state, prelude, name, pool, goal_concl) {
            Some((th, _)) => Some(ExactApplicable(th))
            None => Some(ExactKnownButUnavailable)
          }
        _ => Some(ExactKnownButUnavailable)
      }
    None => None
  }
}

///|
/// Mode-specific theorem resolution for `apply`.
pub fn logic_prop_resolve_apply_theorem(
  state : KernelState,
  prelude : PropPrelude,
  pool : Array[Term],
  goal_concl : Term,
  name : String,
) -> PropApplyTheoremResolution? {
  match logic_prop_theorem_entry(name) {
    Some(entry) =>
      match entry.apply_class {
        Some(ImplicationBacked) =>
          match
            logic_prop_context_apply_theorem(
              state, prelude, name, pool, goal_concl,
            ) {
            Some((th, antecedent)) => Some(Applicable(th, antecedent))
            None => Some(KnownButUnavailable)
          }
        _ => Some(KnownButUnavailable)
      }
    None => None
  }
}
