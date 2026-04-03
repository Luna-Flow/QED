///|
pub struct Goal {
  hyps : Array[Term]
  concl : Term
}

///|
pub fn mk_goal(hyps : Array[Term], concl : Term) -> Goal {
  Goal::{ hyps, concl }
}

///|
pub fn goal_hyp_count(goal : Goal) -> Int {
  goal.hyps.length()
}

///|
pub fn goal_hyps(goal : Goal) -> Array[Term] {
  goal.hyps.copy()
}

///|
pub fn goal_concl(goal : Goal) -> Term {
  goal.concl
}

///|
pub fn tactics_goal_phase0_ready() -> Bool {
  true
}
