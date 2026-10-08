# tactics API

## Purpose

The `tactics` package (`Luna-Flow/QED/tactics`) runs proofs backwards. A `ProofState` holds a root goal and a list of pending subgoals; each `TacticStep` transforms the first pending goal, and when the last goal closes the package replays the recorded steps forward through the `logic` and kernel rules to build the theorem. `ps_qed` returns that theorem only if it proves exactly the root goal. The package depends on `kernel` and `logic`.

The relation between steps and kernel rules is explained in the [tactics design](../design/tactics.md); the [tactics tutorial](../tutorial/tactics.md) proves goals step by step. Users who write proof scripts reach this package through the [prover](prover.md).

## Importing

Add the package to your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/QED/tactics",
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/logic",
  "Luna-Flow/QED/parser",
}
```

The examples on this page are blackbox tests. They refer to this package as `@tactics` and also use `@kernel`, `@logic` and `@parser`, so they import all of these packages.

## Goals

### `Goal`

`Goal` is a sequent to prove: hypotheses and a conclusion, all propositions.

```mbti
pub struct Goal {
  hyps : Array[@kernel.Term]
  concl : @kernel.Term
}
```

Connectives in a goal are the basis terms of the `logic` builders, as produced by the parser.

### `mk_goal`, `goal_hyps`, `goal_concl` and `goal_hyp_count`

These functions build a goal and read it; `goal_hyps` returns a copy.

```mbti
pub fn mk_goal(Array[@kernel.Term], @kernel.Term) -> Goal
pub fn goal_hyps(Goal) -> Array[@kernel.Term]
pub fn goal_concl(Goal) -> @kernel.Term
pub fn goal_hyp_count(Goal) -> Int
```

## Steps

### `TacticStep`

`TacticStep` is one backward proof step.

```mbti
pub enum TacticStep {
  Intro(String)
  Exact(String)
  Apply(String)
  Assumption
  Split
  Left
  Right
}
```

| Step | Current goal | New goals | Closed by |
| --- | --- | --- | --- |
| `Intro(h)` | $\Gamma \vdash a \Rightarrow b$ | $\Gamma, a \vdash b$ with local `h : a` | implication introduction |
| `Intro(x)` | $\Gamma \vdash (\lambda y.\,P) = (\lambda y.\,\top)$ | $\Gamma \vdash P[x/y]$ with `x` fresh | DEDUCT_ANTISYM_RULE and ABS |
| `Exact(n)` | $\Gamma \vdash c$ | none | the local `n`, or catalog theorem `n` in `exact` mode |
| `Apply(n)` | $\Gamma \vdash b$ | $\Gamma \vdash a$ | implication elimination with `n : a ⇒ b` |
| `Assumption` | $\Gamma \vdash c$ with $c \in \Gamma$ | none | the hypothesis |
| `Split` | $\Gamma \vdash a \wedge b$ | $\Gamma \vdash a$, then $\Gamma \vdash b$ | conjunction introduction |
| `Left` | $\Gamma \vdash a \vee b$ | $\Gamma \vdash a$ | disjunction introduction |
| `Right` | $\Gamma \vdash a \vee b$ | $\Gamma \vdash b$ | disjunction introduction |

`Apply(n)` resolves `n` in this order: a local implication whose consequent is the goal; the rule names `imp_elim` (find such an implication among the hypotheses and locals), `imp_intro` (like `Intro` with a hidden local) and `and_intro` (like `Split`); then a catalog name in `apply` mode. The rule names are a tactics-level convenience; the [user manual](../manual.md) lists the theorem names that proof scripts are documented to use. There is no hole step: holes are handled by the prover.

### `step_intro`, `step_exact`, `step_apply`, `step_assumption`, `step_split`, `step_left` and `step_right`

These functions build the corresponding `TacticStep` values.

```mbti
pub fn step_intro(String) -> TacticStep
pub fn step_exact(String) -> TacticStep
pub fn step_apply(String) -> TacticStep
pub fn step_assumption() -> TacticStep
pub fn step_split() -> TacticStep
pub fn step_left() -> TacticStep
pub fn step_right() -> TacticStep
```

## Proof states

### `ProofState`

`ProofState` is the abstract state of a backward proof: the root goal, the ordered pending goals with the data needed to replay them, and the final theorem once there is one.

```mbti
type ProofState
```

States are immutable; every operation returns a new one.

### `ps_init` and `ps_enter_frame`

`ps_init(goal)` starts a proof of `goal` with one pending goal. `ps_enter_frame` is the same operation under the name the prover uses when it opens a branch frame.

```mbti
pub fn ps_init(Goal) -> ProofState
pub fn ps_enter_frame(Goal) -> ProofState
```

### `ps_apply` and `ps_apply_script`

`ps_apply(state, prelude, ps, step)` runs one step on the first pending goal. `ps_apply_script` runs a list of steps and stops at the first error.

```mbti
pub fn ps_apply(@kernel.KernelState, @logic.PropPrelude, ProofState, TacticStep) -> Result[ProofState, TacticExecError]
pub fn ps_apply_script(@kernel.KernelState, @logic.PropPrelude, ProofState, Array[TacticStep]) -> Result[ProofState, TacticExecError]
```

New goals are put in front of the remaining ones, so the first subgoal of `Split` is worked on next. A step that closes a goal replays its evidence through the kernel at once; if the replay fails, the step fails.

### `ps_qed` and `ps_close_frame`

`ps_qed` returns the theorem of a finished proof. `ps_close_frame` is the same operation for a branch frame.

```mbti
pub fn ps_qed(ProofState) -> Result[@kernel.Thm, TacticExecError]
pub fn ps_close_frame(ProofState) -> Result[@kernel.Thm, TacticExecError]
```

Fails with `UnsolvedGoals` while goals are pending. The theorem was checked when the last goal closed: after β-normalisation its hypotheses must match those of the root goal one to one and its conclusion must equal the root conclusion, up to α-equivalence; otherwise the closing step failed with `ProofSynthesisUnavailable`.

### `ps_close_current_with_th`

`ps_close_current_with_th(state, prelude, ps, th)` closes the first pending goal with a theorem you supply, after checking that it proves that goal's conclusion from at most its hypotheses.

```mbti
pub fn ps_close_current_with_th(@kernel.KernelState, @logic.PropPrelude, ProofState, @kernel.Thm) -> Result[ProofState, TacticExecError]
```

Fails with `GoalShapeMismatch` when the theorem does not fit and with `NoGoals` when nothing is pending.

### `ps_isolate_pending_at`

`ps_isolate_pending_at(ps, i)` returns a fresh proof state whose root goal is the pending goal `i`, without the replay context of the original state, or `None` when `i` is out of range.

```mbti
pub fn ps_isolate_pending_at(ProofState, Int) -> ProofState?
```

The prover uses it to run a branch block in its own frame and to keep a failure inside a branch from affecting its siblings.

```moonbit
test "proof state" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let env = @parser.parse_env_push_local(@parser.empty_parse_env(), "p", @kernel.bool_ty())
  let env = @parser.parse_env_push_local(env, "q", @kernel.bool_ty())
  let g = @parser.parse_goal_with_env(st, env, "⊢ p ∧ q -> q ∧ p").unwrap()
  let ps = @tactics.ps_init(@tactics.mk_goal(@parser.parsed_goal_hyps(g), @parser.parsed_goal_concl(g)))
  let ps = @tactics.ps_apply_script(st, pre, ps, [
    @tactics.step_intro("h"),
    @tactics.step_split(),
  ]).unwrap()
  inspect(@tactics.ps_goal_count(ps), content="2")
  inspect(@tactics.ps_qed(ps) is Err(@tactics.UnsolvedGoals), content="true")
  let ps = @tactics.ps_apply_script(st, pre, ps, [
    @tactics.step_exact("and_elim_r"),
    @tactics.step_exact("and_elim_l"),
  ]).unwrap()
  let th = @tactics.ps_qed(ps).unwrap()
  inspect(@kernel.thm_hyp_count(th), content="0")
  // nothing is left to do
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_split()) is Err(@tactics.NoGoals), content="true")
}
```

## Observing a proof

### `ps_goal_count`, `ps_current_goal` and `ps_pending_goal_at`

`ps_goal_count` is the number of pending goals. `ps_current_goal` returns the first one and `ps_pending_goal_at` the one at an index.

```mbti
pub fn ps_goal_count(ProofState) -> Int
pub fn ps_current_goal(ProofState) -> Goal?
pub fn ps_pending_goal_at(ProofState, Int) -> Goal?
```

### `ps_root_goal`

`ps_root_goal` returns the goal the proof started from.

```mbti
pub fn ps_root_goal(ProofState) -> Goal
```

### `LocalHyp`, `local_hyp_name` and `local_hyp_term`

`LocalHyp` is a named hypothesis introduced by `Intro`, as the user sees it.

```mbti
type LocalHyp

pub fn local_hyp_name(LocalHyp) -> String
pub fn local_hyp_term(LocalHyp) -> @kernel.Term
```

### `ps_current_local_hyps` and `ps_current_branch_path`

These functions return the locals and the branch path of the first pending goal. The branch path lists, from the root, which subgoal was taken at each `Split` (1 or 2), `Left` or `Right` (always 1).

```mbti
pub fn ps_current_local_hyps(ProofState) -> Array[LocalHyp]
pub fn ps_current_branch_path(ProofState) -> Array[Int]
```

### `ProofGoalView`, `ps_current_focus` and `ps_pending_focus_at`

`ProofGoalView` bundles a pending goal with its locals and branch path. The two functions return the view of the first pending goal or of the goal at an index.

```mbti
type ProofGoalView

pub fn ps_current_focus(ProofState) -> ProofGoalView?
pub fn ps_pending_focus_at(ProofState, Int) -> ProofGoalView?
pub fn proof_goal_view_goal(ProofGoalView) -> Goal
pub fn proof_goal_view_locals(ProofGoalView) -> Array[LocalHyp]
pub fn proof_goal_view_branch_path(ProofGoalView) -> Array[Int]
```

### `ProofStateSnapshot` and `ps_snapshot`

`ps_snapshot` captures the root goal, the number of pending goals and the current focus in one value, for diagnostics.

```mbti
type ProofStateSnapshot

pub fn ps_snapshot(ProofState) -> ProofStateSnapshot
pub fn proof_state_snapshot_root_goal(ProofStateSnapshot) -> Goal
pub fn proof_state_snapshot_pending_goal_count(ProofStateSnapshot) -> Int
pub fn proof_state_snapshot_current(ProofStateSnapshot) -> ProofGoalView?
```

```moonbit
test "observe" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let env = @parser.parse_env_push_local(@parser.empty_parse_env(), "p", @kernel.bool_ty())
  let g = @parser.parse_goal_with_env(st, env, "⊢ p -> p ∧ p").unwrap()
  let ps = @tactics.ps_init(@tactics.mk_goal(@parser.parsed_goal_hyps(g), @parser.parsed_goal_concl(g)))
  let ps = @tactics.ps_apply_script(st, pre, ps, [@tactics.step_intro("h"), @tactics.step_split()]).unwrap()
  assert_eq(@tactics.ps_current_local_hyps(ps).map(@tactics.local_hyp_name), ["h"])
  assert_eq(@tactics.ps_current_branch_path(ps), [1])
  let second = @tactics.ps_pending_focus_at(ps, 1).unwrap()
  assert_eq(@tactics.proof_goal_view_branch_path(second), [2])
  let snap = @tactics.ps_snapshot(ps)
  inspect(@tactics.proof_state_snapshot_pending_goal_count(snap), content="2")
}
```

## Replay context

These enums describe how a pending goal will be replayed when it closes. They appear in the interface because pending goals carry them; callers do not build them.

### `PendingRefine`

`PendingRefine` records a backward step to undo forwards: an `apply` of a local implication term (`ImpBackwardTerm`) or of an implication theorem (`ImpBackwardTheorem`), or an `intro` on a quantified goal with the user's binder and a fresh replay binder (`AbsBackwardTerm`).

```mbti
pub enum PendingRefine {
  ImpBackwardTerm(@kernel.Term)
  ImpBackwardTheorem(@kernel.Thm)
  AbsBackwardTerm(@kernel.Term, @kernel.Term)
}
```

### `SplitRole`

`SplitRole` marks a goal as the left or right half of a `Split`; the right half receives the left half's theorem when it closes.

```mbti
pub enum SplitRole {
  SplitNone
  SplitLeft(@kernel.Term)
  SplitRight(@kernel.Term, @kernel.Thm?)
}
```

### `OrContext`

`OrContext` marks a goal produced by `Left` or `Right`, with the full disjunction and the other branch.

```mbti
pub enum OrContext {
  OrNone
  OrPendingLeft(@kernel.Term, @kernel.Term)
  OrPendingRight(@kernel.Term, @kernel.Term)
}
```

## Errors

### `TacticExecError`

`TacticExecError` is the failure of a step or of `ps_qed`.

```mbti
pub enum TacticExecError {
  UnknownName(String)
  GoalShapeMismatch(String)
  ApplyMismatch(String)
  NoGoals
  UnsolvedGoals
  ProofSynthesisUnavailable(String)
  Logic(@kernel.LogicError)
}
```

| Constructor | Meaning |
| --- | --- |
| `UnknownName(n)` | `n` is neither a local nor a catalog name. |
| `GoalShapeMismatch(msg)` | The goal does not have the shape the step needs, or `exact` was given a witness that does not close it. |
| `ApplyMismatch(msg)` | `apply` was given something that is not an implication ending in the goal. |
| `NoGoals` | A step was applied to a finished proof. |
| `UnsolvedGoals` | `ps_qed` was called with goals pending. |
| `ProofSynthesisUnavailable(msg)` | Replay could not build a theorem for the root goal. |
| `Logic(e)` | A kernel or logic rule failed during replay. |

### `tactic_goal_shape_mismatch` and `tactic_no_goals`

These functions build the two errors that callers outside the package raise themselves: the prover uses them when a branch block does not fit its goal.

```mbti
pub fn tactic_goal_shape_mismatch(String) -> TacticExecError
pub fn tactic_no_goals() -> TacticExecError
```

```moonbit
test "errors" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let env = @parser.parse_env_push_local(@parser.empty_parse_env(), "p", @kernel.bool_ty())
  let g = @parser.parse_goal_with_env(st, env, "⊢ p -> p").unwrap()
  let ps = @tactics.ps_init(@tactics.mk_goal(@parser.parsed_goal_hyps(g), @parser.parsed_goal_concl(g)))
  let ps = @tactics.ps_apply(st, pre, ps, @tactics.step_intro("h")).unwrap()
  // `truth` is a catalog name, but not an implication
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_apply("truth")) is Err(@tactics.ApplyMismatch(_)), content="true")
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_exact("nope")) is Err(@tactics.UnknownName("nope")), content="true")
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_split()) is Err(@tactics.GoalShapeMismatch(_)), content="true")
  inspect(@tactics.ps_apply(st, pre, ps, @tactics.step_assumption()) is Ok(_), content="true")
}
```
