///|
pub struct Goal {
  hyps : Array[@kernel.Term]
  concl : @kernel.Term
}

///|
pub fn mk_goal(hyps : Array[@kernel.Term], concl : @kernel.Term) -> Goal {
  Goal::{ hyps, concl }
}

///|
pub fn goal_hyp_count(goal : Goal) -> Int {
  goal.hyps.length()
}

///|
pub fn goal_concl(goal : Goal) -> @kernel.Term {
  goal.concl
}

///|
pub fn tactics_goal_phase0_ready() -> Bool {
  true
}
