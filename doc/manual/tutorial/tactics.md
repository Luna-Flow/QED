# tactics tutorial

This tutorial drives a proof state by hand with the `tactics` package: you state a goal, apply steps one at a time, look at the pending goals in between, and collect the kernel theorem at the end. It is what the prover does for every proof script, without the parsing and scheduling.

## Quick start

Import the packages in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/logic",
  "Luna-Flow/QED/parser",
  "Luna-Flow/QED/tactics",
}
```

Prove $\vdash p \Rightarrow p$ with `intro` and `exact`:

```moonbit
fn goal_of(st : @kernel.KernelState, locals : Array[String], src : String) -> @tactics.Goal {
  let mut env = @parser.empty_parse_env()
  for name in locals {
    env = @parser.parse_env_push_local(env, name, @kernel.bool_ty())
  }
  let g = @parser.parse_goal_with_env(st, env, src).unwrap()
  @tactics.mk_goal(@parser.parsed_goal_hyps(g), @parser.parsed_goal_concl(g))
}

test "quick start" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_init(goal_of(st, ["p"], "⊢ p -> p"))
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_intro("h")).unwrap()
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_exact("h")).unwrap()
  let th = @tactics.ps_qed(ps).unwrap()
  inspect(@kernel.thm_hyp_count(th), content="0")
}
```

`goal_of` is a small helper used throughout this page: it declares boolean locals and parses a goal. Every step takes the kernel state and the prelude, because it may call kernel rules.

## Everyday tasks

### Watch the goals change

After each step, `ps_current_goal` and `ps_current_local_hyps` show what is left:

```moonbit
test "watch" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_init(goal_of(st, ["x"], "⊢ x -> x ∧ x"))
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_intro("h")).unwrap()
  // the goal is now  x ⊢ x ∧ x  with the local h : x
  let g = @tactics.ps_current_goal(ps).unwrap()
  inspect(@tactics.goal_hyp_count(g), content="1")
  assert_eq(@tactics.ps_current_local_hyps(ps).map(@tactics.local_hyp_name), ["h"])
  // split leaves two goals, x and x, on branches 1 and 2
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_split()).unwrap()
  inspect(@tactics.ps_goal_count(ps), content="2")
  assert_eq(@tactics.ps_current_branch_path(ps), [1])
  let ps = @tactics.ps_apply_script(st, pre, ps, [@tactics.step_exact("h"), @tactics.step_exact("h")]).unwrap()
  inspect(@tactics.ps_qed(ps) is Ok(_), content="true")
}
```

This is the script `demo_and` from `examples/demo_and.qed`, step by step.

### Use catalog theorems

`exact` and `apply` also accept theorem names from the catalog of the `logic` package. Commutativity of conjunction uses the conjunction in context:

```moonbit
test "and_comm" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_init(goal_of(st, ["p", "q"], "⊢ p ∧ q -> q ∧ p"))
  let ps = @tactics.ps_apply_script(st, pre, ps, [
    @tactics.step_intro("h"),
    @tactics.step_split(),
    @tactics.step_exact("and_elim_r"), // q, from p ∧ q in context
    @tactics.step_exact("and_elim_l"), // p, from p ∧ q in context
  ]).unwrap()
  inspect(@tactics.ps_qed(ps) is Ok(_), content="true")
}
```

### Work backwards with `apply`

`apply` replaces a goal $b$ by $a$ when an implication $a \Rightarrow b$ is available. This is corpus case `t2`, $\vdash p \wedge q \Rightarrow p$:

```moonbit
test "apply" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_init(goal_of(st, ["p", "q"], "⊢ p ∧ q -> p"))
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_intro("h")).unwrap()
  // and_elim_l as an implication: from p ∧ q infer p, so the goal becomes p ∧ q
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_apply("and_elim_l")).unwrap()
  inspect(@tactics.ps_goal_count(ps), content="1")
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_exact("h")).unwrap()
  inspect(@tactics.ps_qed(ps) is Ok(_), content="true")
}
```

### Choose a side of a disjunction

`left` and `right` commit to one side. This is corpus case `t4`, $p \vdash p \vee q$:

```moonbit
test "left" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_init(goal_of(st, ["p", "q"], "p ⊢ p ∨ q"))
  let ps = @tactics.ps_apply_script(st, pre, ps, [@tactics.step_left(), @tactics.step_assumption()]).unwrap()
  inspect(@tactics.ps_qed(ps) is Ok(_), content="true")
  // choosing the wrong side leaves a goal that cannot be closed
  let wrong = @tactics.ps_apply(st, pre, @tactics.ps_init(goal_of(st, ["p", "q"], "p ⊢ p ∨ q")), @tactics.step_right()).unwrap()
  let stuck = @tactics.ps_apply(st, pre, wrong, @tactics.step_assumption())
  inspect(stuck is Err(@tactics.GoalShapeMismatch(_)), content="true")
}
```

### Read the errors

A step that does not fit fails with a reason; the previous state is unchanged and can be used again:

```moonbit
test "errors" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let ps = @tactics.ps_apply(st, pre, @tactics.ps_init(goal_of(st, ["x"], "⊢ x -> x ∨ x")), @tactics.step_intro("h")).unwrap()
  let ps_left = @tactics.ps_apply(st, pre, ps, @tactics.step_left()).unwrap()
  // `truth` proves T, not x
  match @tactics.ps_apply(st, pre, ps_left, @tactics.step_exact("truth")) {
    Err(@tactics.GoalShapeMismatch(msg)) => inspect(msg, content="exact witness does not directly close current goal")
    _ => fail("expected a goal-shape mismatch")
  }
  // `or_intro_l` cannot be used with exact, only with apply
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_exact("or_intro_l")) is Err(@tactics.GoalShapeMismatch(_)), content="true")
  inspect(@tactics.ps_qed(ps) is Err(@tactics.UnsolvedGoals), content="true")
}
```

The first failure is the `bad_branch` example of the [user manual](../manual.md); the prover reports it with the step number and branch path.

## Going further

**Close a goal with your own theorem.** `ps_close_current_with_th(state, pre, ps, th)` closes the current goal with a theorem built elsewhere, for example with the `logic` package; it checks that the theorem fits the goal.

**Work on one branch in isolation.** `ps_isolate_pending_at(ps, i)` makes a fresh proof state for pending goal `i`. The prover uses it to run a `{ ... }` branch block on its own, so a failure inside one branch is reported against that branch only.

**Prove a quantified goal.** For a goal in HOL's encoding of $\forall x.\,P$, that is $(\lambda x.\,P) = (\lambda x.\,\top)$, `intro x` strips the quantifier and the replay rebuilds it with ABS. Goals written with `forall` in a script are handled differently, as free variables; see the [parser design](../design/parser.md).

**Let the prover do it.** The [prover tutorial](prover.md) runs the same steps from a text script and adds structured diagnostics and unfinished proofs.

## Common pitfalls

- **Forgetting the prelude.** Goals with `T`, `F` or catalog names need `install_prop_prelude` in the state passed to every step.
- **Expecting `exact` to start a backward step.** `exact` closes a goal or fails. Use `apply` for implications such as `or_intro_l`.
- **Shadowed locals.** A local named like a catalog theorem hides the theorem: after `intro truth`, `exact truth` refers to the local.
- **Case analysis.** There is no step that uses a disjunction in the hypotheses; the [logic design](../design/logic.md) explains why.
- **Assuming `ps_qed` re-checks.** The root check runs when the last goal closes; `ps_qed` only reports the result or `UnsolvedGoals`.

## Next steps

- The [tactics API](../api/tactics.md) lists every function and the replay context types.
- The [tactics design](../design/tactics.md) explains justifications and why invalid steps cannot produce false theorems.
- The [prover tutorial](prover.md) runs the same proofs from scripts.
