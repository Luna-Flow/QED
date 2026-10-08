# tactics design

The `tactics` package lets a user prove a goal backwards, by reducing it to simpler goals, while every theorem is still built forwards by the kernel. This page explains the LCF view of tactics as theorem transformers, how QED records the forward half of each step as data instead of closures, and why an incorrect tactic can make a proof fail but never make it succeed wrongly.

## Design goal

- Offer goal-directed steps (`intro`, `split`, `left`, `right`, `apply`, `exact`, `assumption`) whose meaning matches natural deduction.
- Produce a kernel `Thm` for exactly the goal the user stated, or fail with a reason and the location of the failing goal.
- Hold no authority: the package only calls `logic` and kernel functions to build theorems.

## Mathematical background

### Tactics as theorem transformers

In LCF a goal is a sequent $\Gamma \vdash c$ still to be proved, and a tactic is a function

$$
\mathsf{tac} : \mathit{goal} \to \mathit{goal}^{*} \times (\mathit{thm}^{*} \to \mathit{thm})
$$

that returns subgoals $g_1, \dots, g_n$ and a *justification* $j$. The tactic is *valid* when, for theorems $t_1, \dots, t_n$ that prove $g_1, \dots, g_n$, the theorem $j(t_1, \dots, t_n)$ proves the original goal.[^gordon] Running a proof means applying tactics until no goals remain, then composing the justifications bottom-up, starting from theorems that close leaves.

[^gordon]: M. Gordon, R. Milner, C. Wadsworth, *Edinburgh LCF*, LNCS 78, 1979. A sequent $\Gamma' \vdash c'$ *proves* a goal $\Gamma \vdash c$ when $c' \equiv_\alpha c$ and $\Gamma' \subseteq \Gamma$.

The key property is that validity is a matter of *correctness*, not of *soundness*. A justification can only build theorems by calling kernel rules. If a tactic is invalid, its justification produces a theorem for some other goal, or fails; it cannot produce a false theorem. LCF therefore checks validity at the end, and QED does the same.

### The justifications of QED's steps

Each step below is a valid tactic; the justification is the kernel derivation in the right column.

| Step | Goal | Subgoals | Justification |
| --- | --- | --- | --- |
| `intro h` | $\Gamma \vdash a \Rightarrow b$ | $\Gamma, a \vdash b$ | $t \mapsto$ discharge $a$ from $t$ (implication introduction) |
| `split` | $\Gamma \vdash a \wedge b$ | $\Gamma \vdash a$, $\Gamma \vdash b$ | $(t_1, t_2) \mapsto$ conjunction introduction |
| `left` | $\Gamma \vdash a \vee b$ | $\Gamma \vdash a$ | $t \mapsto$ disjunction introduction on the left |
| `right` | $\Gamma \vdash a \vee b$ | $\Gamma \vdash b$ | $t \mapsto$ disjunction introduction on the right |
| `apply h`, $h : a \Rightarrow b \in \Gamma$ | $\Gamma \vdash b$ | $\Gamma \vdash a$ | $t \mapsto$ modus ponens with $\{a \Rightarrow b\} \vdash a \Rightarrow b$ |
| `exact h`, `assumption` | $\Gamma \vdash c$, $c \in \Gamma$ | none | ASSUME $c$, weakened to $\Gamma$ |
| `exact n` | $\Gamma \vdash c$ | none | the catalog theorem for $n$, weakened to $\Gamma$ |

Validity of each line is the corresponding natural-deduction rule, derived in the [logic design](logic.md). For `intro` on an implication the subgoal has $a$ among its hypotheses, so implication introduction can discharge it, and the result has hypotheses $\Gamma$ again.

`intro x` also applies to a goal of the form $(\lambda y.\,P) = (\lambda y.\,\top)$, with $\top$ the constant `T`, which is HOL's encoding of $\forall y.\,P$. The kernel reads the two abstractions back with a generated binder name $z$ (`_b0`, `_b1`, ...) that is fresh for the conclusion, and the subgoal is $\Gamma \vdash P[z/y]$ with $z$ now free; the local `x` names it. When the subgoal is proved, the justification renames $z$ to a variable $x'$ chosen fresh against the goal, its locals and its hypotheses, and abstracts:

$$
\frac{\dfrac{\dfrac{\Gamma \vdash P[z/y] \qquad \vdash \top}{\Gamma \vdash P[z/y] = \top}\;\textsf{DEDUCT\_ANTISYM\_RULE}}{\Gamma \vdash P[x'/y] = \top}\;\textsf{INST}\,[z \mapsto x']}{\Gamma \vdash (\lambda x'.\,P[x'/y]) = (\lambda x'.\,\top)}\;\textsf{ABS}
$$

The last line is the goal up to α-equivalence. When $z$ does not occur free in $\Gamma$, INST leaves $\Gamma$ unchanged and ABS applies, because $x'$ is fresh by construction. But $z$ is only fresh for the conclusion. If a hypothesis happens to contain a free variable with the generated name, the subgoal $\Gamma \vdash P[z/y]$ speaks about that variable, a step may close it using the hypothesis, and the replay then fails with `Logic(VarFreeInHyp)`. The step is then not a valid tactic in the LCF sense, but the failure is caught by the kernel, as described below. Goals from theorem scripts never reach this case, because the parser lowers `forall` by dropping the quantifier, not into this encoding.

## Design decisions

### Justifications as data

**Problem.** LCF represents a justification as a closure. A closure cannot be inspected, so it cannot report where in a proof it failed, and it captures the whole context it was built in.

**Choice.** A pending goal carries its justification as data: an implication prefix (hypotheses to discharge), a refinement chain of `PendingRefine` values (backward `apply` and quantifier steps to undo), a `SplitRole` (left or right half of a conjunction) and an `OrContext` (which side of a disjunction was chosen). When a goal closes, `finish_goal_evidence` interprets that data: it replays the refinement chain, then wraps disjunctions, merges conjunction halves, discharges the implication prefix, and finally undoes quantifier steps.

**Why.** The data is the defunctionalised form of the closure: each constructor corresponds to one justification in the table above, and the interpreter applies them. It can be inspected for diagnostics, it is immutable, and two proof states can share structure safely.

### Replay at every close, check at the root

**Problem.** If the forward replay waited for the very end, an invalid step early in a proof would be reported only at `ps_qed`, far from its cause.

**Choice.** Evidence is replayed as soon as a goal closes. The first half of a `split` stores its theorem in the second half's `SplitRole`; when the second half closes, both are merged. When the last goal closes, the theorem is compared with the root goal: after β-normalisation, its hypotheses must match the root hypotheses one to one and its conclusion must equal the root conclusion, both up to α-equivalence. Only then is it stored as the final theorem.

**Why.** Failures appear at the step that causes them, and the final comparison is exactly LCF's validity check: if every step were valid it would always succeed, and if some step is not, the user gets `ProofSynthesisUnavailable` instead of a theorem for the wrong statement.

### Two name spaces, one order

`exact n` and `apply n` look up `n` first among the locals introduced by `intro`, then among the catalog names of the `logic` package. A local always wins and never falls back to a catalog name, so a local named `truth` cannot be mistaken for the theorem `truth`. The catalog is consulted in the mode of the step: `exact` uses only names that can close a goal outright, and `apply` only names that are implications. A name used in the wrong mode is reported as a mismatch, not as an unknown name.

### No hole step

A proof with a gap is not a proof. The tactics layer has no step that leaves a goal open, so it cannot produce a state that pretends to be finished. Holes are a frontend concept: the prover stops at a hole and reports an unfinished proof with the goal at that point.

## Correctness and invariants

- **Soundness.** Every theorem is built by `logic` and kernel functions; the tactics layer cannot construct a `Thm`. A bug here makes a proof fail or report the wrong error, never succeed with a false theorem.
- **Root fidelity.** A proof state has a final theorem only if that theorem proves the root goal, up to β-normal form and α-equivalence, with exactly the root hypotheses.
- **Goal order.** New subgoals are placed in front of the remaining goals, in order. Together with `Split` storing the left half's theorem in the right half, this gives the left-to-right evaluation that the prover's branch blocks rely on.
- **Branch paths.** Each pending goal records the path of choices from the root: `Split` appends 1 or 2, `Left` and `Right` append 1. The prover and the CLI print this path on failure.
- **Persistence.** `ps_apply` never changes its argument; a failed step leaves the previous state usable.

## Alternatives rejected

- **Closures for justifications.** Simpler to write, but opaque for diagnostics and harder to test.
- **Building theorems only at `ps_qed`.** Fewer kernel calls, but errors would surface far from their cause.
- **Implicit `exact`-to-`apply` fallback.** Letting `exact` silently start a backward step when a name is an implication would make scripts harder to read and errors harder to place. The modes are separate.
- **Metavariables.** Leaving parts of a goal to be filled later, as Isabelle or Lean do, would need unification and a notion of incomplete theorem in the kernel. The shipped subset does not need it.

## Boundaries

- Propositional steps only, plus `intro` on the HOL encoding of a universal quantifier. No rewriting, no case analysis on disjunctions, no induction.
- No proof search: every step is given by the user. `assumption` and `apply imp_elim` only search the current hypotheses.
- No parsing and no scheduling of branch blocks; the [prover](prover.md) does both.
- No holes and no partial theorems.
