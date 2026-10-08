# prover tutorial

This tutorial runs theorem scripts from MoonBit with the `prover` package and reads its three kinds of result: a proved theorem, a structured failure, and an unfinished proof. All scripts come from `examples/` and the regression corpus, so the outputs shown are the ones the tests check.

## Quick start

Import the kernel and the prover in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/tactics",
  "Luna-Flow/QED/prover",
}
```

Run the smallest script, `examples/truth_file.qed`:

```moonbit
test "quick start" {
  let st = @kernel.empty_kernel_state()
  let src = "theorem truth_file : ⊢ T := by exact truth"
  match @prover.prove_theorem_script_detailed(st, src, @prover.default_prover_options()) {
    Proved(ok) => {
      inspect(ok.theorem_name, content="truth_file")
      inspect(@kernel.thm_hyp_count(ok.thm), content="0")
    }
    _ => fail("expected a proof")
  }
}
```

`default_prover_options()` installs the propositional prelude, so `T` and the catalog theorem `truth` are available on an empty state. The result's `thm` is a kernel theorem.

## Everyday tasks

### Prove with binders and branch blocks

Header binders declare locals of the goal; branch blocks after `split` prove each half separately. This is `examples/and_comm.qed`:

```moonbit
test "and_comm" {
  let src =
    #|theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
    #|  intro h
    #|  split { exact and_elim_r } { exact and_elim_l }
  let r = @prover.prove_theorem_script(@kernel.empty_kernel_state(), src, @prover.default_prover_options())
  guard r is Ok((_, th)) else { fail("expected a proof") }
  inspect(@kernel.thm_hyp_count(th), content="0")
}
```

`prove_theorem_script` returns `Ok((state, thm))` or an error, for callers that only care about the theorem.

### Locate a failure

When a step fails, the result says which step, on which branch, with which goal and locals. This is `examples/bad_branch.qed`:

```moonbit
test "failure" {
  let src =
    #|theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
    #|  intro h
    #|  left { exact truth }
  let r = @prover.prove_theorem_script_detailed(@kernel.empty_kernel_state(), src, @prover.default_prover_options())
  guard r is Failed(f) else { fail("expected a failure") }
  inspect(f.kind is Tactic, content="true")
  inspect(f.detail, content="GoalShapeMismatch(exact witness does not directly close current goal)")
  assert_eq(f.step_index, Some(3))
  assert_eq(f.branch_path, [1])
  assert_eq(f.step_src, Some("exact truth"))
  assert_eq(f.local_hyps.map(h => h.name), ["h"])
}
```

Step 3 is `exact truth` (after `intro h` and `left`), on branch 1 of the `left` block. The goal at that point is `x`, which `truth` does not prove.

### Report an unfinished proof

A `hole` marks a gap. The prover stops there and reports the goal the hole stands for; no theorem is produced. This is `examples/unfinished_branch.qed`:

```moonbit
test "unfinished" {
  let src =
    #|theorem unfinished_branch (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by
    #|  intro h
    #|  right { right { hole h1 } }
  let r = @prover.prove_theorem_script_detailed(@kernel.empty_kernel_state(), src, @prover.default_prover_options())
  guard r is Unfinished(u) else { fail("expected an unfinished proof") }
  assert_eq(u.hole_name, Some("h1"))
  assert_eq(u.branch_path, [1, 1])
  inspect(u.detail, content="proof contains an unfinished hole")
  inspect(@tactics.goal_hyp_count(u.current_goal), content="1")
}
```

`current_goal` is $x \vdash x$: fill the hole with `exact h` to finish the proof.

### Check a whole file

`prove_theorem_file_results_detailed` checks every theorem of a file and keeps going after a failure or a hole. This is `examples/multi_with_hole.qed`:

```moonbit
test "file" {
  let src =
    #|theorem before_hole : ⊢ T := by exact truth
    #|qed
    #|
    #|theorem unfinished_demo (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by
    #|  intro h
    #|  right { right { hole h1 } }
    #|qed
    #|
    #|theorem after_hole : ⊢ T := by exact truth
    #|qed
  let r = @prover.prove_theorem_file_results_detailed(@kernel.empty_kernel_state(), src, @prover.default_prover_options())
  guard r is FileChecked(report) else { fail("expected a report") }
  let names = report.items.map(item => match item {
    ProverItemProved(ok) => "ok " + ok.theorem_name
    ProverItemFailed(f) => "error " + f.detail
    ProverItemUnfinished(u) => "unfinished " + u.theorem_name
  })
  assert_eq(names, ["ok before_hole", "unfinished unfinished_demo", "ok after_hole"])
}
```

## Going further

**Run against your own state.** Pass `@prover.prover_options(false)` to skip the prelude and run against a state you prepared, for example one with extra constants declared through the kernel. Without the prelude, `T` is unknown and the run fails with a `Sig` diagnostic:

```moonbit
test "no prelude" {
  let src = "theorem t : ⊢ T := by exact truth"
  let r = @prover.prove_theorem_script_detailed(@kernel.empty_kernel_state(), src, @prover.prover_options(false))
  guard r is Failed(f) else { fail("expected a failure") }
  inspect(f.kind is Sig, content="true")
  inspect(f.detail, content="UnknownConst")
}
```

**Use the corpus.** `positive_corpus_cases()` and its siblings return the scripts the tests run, with their expected outcomes. They are a ready-made set of examples and a regression suite for anything you build on top of the prover.

**Render results.** The [cmd](cmd.md) package turns these results into the `ok`, `error[...]` and `warning[unfinished]` lines of the command-line tool; reuse its renderer if you need the same text.

## Common pitfalls

- **Expecting theorems from holes.** An `Unfinished` result has no theorem, and `prove_theorem_script` returns it as an error.
- **Citing earlier theorems.** Theorems proved earlier in a file are not available to later ones; only catalog names are.
- **Forgetting `qed` between theorems.** In a file with several theorems, each one but possibly the last must be followed by a `qed` line, or the file fails to parse.
- **Free names in goals.** A name in a goal must be a header binder, a constant of the state, or `T`/`F` from the prelude. Use binders such as `(x : bool)` for variables.
- **Raw `forall` inside terms.** `forall` is accepted only at the start of the goal.

## Next steps

- The [prover API](../api/prover.md) lists every result field and the corpus types.
- The [prover design](../design/prover.md) explains why there are three outcomes and how branch blocks are scheduled.
- The [user manual](../manual.md) has the support matrix and the full list of corpus examples; the [syntax guide](../syntax.md) is the script reference.
- The [cmd tutorial](cmd.md) runs the same scripts from the command line.
