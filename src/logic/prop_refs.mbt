///|
pub enum PropRefResolution {
  LocalFact(Term)
  NamedTheorem(Thm)
  ContextDerived(Thm, Term)
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
  match logic_prop_named_theorem(state, prelude, name, goal_concl) {
    Some(th) => return Some(NamedTheorem(th))
    None => ()
  }
  match logic_prop_context_theorem(state, prelude, name, pool, goal_concl) {
    Some((th, antecedent)) => Some(ContextDerived(th, antecedent))
    None => None
  }
}
