# cmd tutorial

This tutorial checks theorem-script files with the command-line tool `qed-cmd`. You run the examples shipped in `examples/`, read successes, errors and unfinished proofs, and use the exit status in scripts. No MoonBit code is needed.

| I want to | Use |
| --- | --- |
| Check a file of theorem scripts | `moon run src/cmd <file>`, or `qed-cmd <file>` once built |
| See the conclusion of every proved theorem | `-d`, as in `moon run src/cmd -- -d <file>` |
| Accept unfinished proofs while working | `--no-warn` |
| Fail a CI job on any error or hole | the exit status, without `--no-warn` |

## Quick start

From the repository root, with the MoonBit toolchain installed:

```bash
moon run src/cmd examples/truth_file.qed
```

```text
ok truth_file
```

The file contains one theorem:

```text
theorem truth_file : ⊢ T := by exact truth
```

`moon run src/cmd` builds and runs the tool. Arguments for the tool itself go after `--`, as in `moon run src/cmd -- -d <file>`; once built as a standalone executable, the same call is `qed-cmd -d <file>`.

## Everyday tasks

### Check several theorems

Separate theorems with a line containing `qed`. `examples/multi_theorems.qed`:

```text
theorem truth_demo : ⊢ T := by exact truth
qed

theorem id_bool_demo (x : bool) : ⊢ x -> x := by
  intro h
  exact h
qed

theorem dup_bool_demo (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
qed
```

```bash
moon run src/cmd examples/multi_theorems.qed
```

```text
ok truth_demo
ok id_bool_demo
ok dup_bool_demo
```

The exit status is 0.

### See what was proved

`-d` prints the conclusion of each theorem, in the kernel's structural notation:

```bash
moon run src/cmd -- -d examples/truth_file.qed
```

```text
ok truth_file: Const(T#1 : bool)
```

For larger goals the conclusion is long, because connectives are printed as their definitions.

### Read an error

`examples/bad_branch.qed` tries to prove the left branch `x` of `x ∨ x` with `truth`:

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
```

```bash
moon run src/cmd examples/bad_branch.qed
```

```text
error[tactic] examples/bad_branch.qed (bad_branch): GoalShapeMismatch(exact witness does not directly close current goal)
step: 3
branch: 1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
```

Step 3 is `exact truth`; the goal there is `x` under the hypothesis `x`, with the local `h`. Replacing `exact truth` with `exact h` proves the theorem. The exit status is 1.

### Leave a hole and keep going

`hole` marks a gap. The tool reports it as a warning and checks the remaining theorems. `examples/multi_with_hole.qed`:

```bash
moon run src/cmd examples/multi_with_hole.qed
```

```text
ok before_hole
warning[unfinished] examples/multi_with_hole.qed (unfinished_demo): proof contains an unfinished hole
theorem: unfinished_demo
step: 4
branch: 1.1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
hole: h1
message: proof contains an unfinished hole
ok after_hole
```

The status is 1, because a file with holes is not finished. During development, allow warnings:

```bash
moon run src/cmd -- --no-warn examples/multi_with_hole.qed
echo $?
```

```text
0
```

The output is the same; only the status changes.

## Going further

**Use it in CI.** Run the tool on each proof file and rely on the status: 0 means every theorem was proved. Leave out `--no-warn` in CI so that holes fail the build.

**Build a standalone binary.** `moon build` produces the tool for the default target; on the native target the executable can be called as `qed-cmd -d --no-warn <file>` without `--`.

**Go beyond the subset.** The tool accepts what the prover accepts: the steps and theorem names listed in the [syntax guide](../syntax.md) and the support matrix of the [user manual](../manual.md). For programmatic use, call the [prover](prover.md) from MoonBit.

## Common pitfalls

- **Forgetting `--` with `moon run`.** `moon run src/cmd -d file` passes `-d` to `moon`, not to the tool.
- **Missing `qed` separators.** In a file with several theorems, a missing `qed` makes the file fail to parse (`error[parse] <file>: offset …: missing qed before next theorem`), and nothing is checked.
- **Free names.** A goal may only mention header binders such as `(x : bool)`, `T` and `F`; another name is an unknown constant and the theorem fails with `error[sig] <file> (<name>): UnknownConst`.
- **Expecting `--no-warn` to hide warnings.** It changes the status only.
- **Citing an earlier theorem.** Theorems in a file are independent; `exact before_hole` does not refer to the theorem above.

## Next steps

- The [cmd API](../api/cmd.md) lists the options, output lines and exit codes.
- The [cmd design](../design/cmd.md) explains the output contract.
- The [syntax guide](../syntax.md) and the [user manual](../manual.md) describe what scripts may contain.
