# Syntax guide

- Status: active
- Audience: users, contributors
- Authority: user-facing syntax reference for current shipped input surface; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ), current code/tests, and [User manual](manual.md)
- Scope: current theorem-script surface syntax, CLI-facing file shape, supported proof steps, and known unsupported forms
- Last reviewed: 2026-04-20

This document is a quick reference for QED's current shipped user input syntax.

It answers only one question: what kind of theorem script does `src/cmd` currently accept. For
capability boundaries, the support matrix, failure semantics, and the implementation contract,
[User manual](manual.md) remains the main entry point.

## Quick start

The current command-line entry point is:

```bash
moon run src/cmd <file>
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

`-d` prints the full conclusion summary. `--no-warn` returns a success exit code when there are only
warnings and no errors. When launching through `moon run`, use `--` to forward the remaining
arguments to the QED CLI; once compiled into a standalone executable, you can run
`qed-cmd -d --no-warn <file>` directly.

The input is a theorem-script file, for example:

```text
theorem truth_file : ⊢ T := by exact truth
```

Runnable examples in the repository:

- `examples/truth_file.qed`
- `examples/demo_and.qed`
- `examples/and_comm.qed`
- `examples/multi_theorems.qed`
- `examples/multi_with_hole.qed`
- `examples/bad_branch.qed`
- `examples/unfinished_branch.qed`

The repository root also has `prelude/`, which holds theorem asset files that can be run directly;
they are runnable scripts, not the public surface of the current theorem-name catalog.

## File shape

The current shipped theorem script shape is:

```text
theorem <name> [(binder...)] : <goal> := by <steps>
```

When a file contains several theorems, end each preceding theorem block with a lowercase `qed`:

```text
theorem t1 : ⊢ T := by exact truth
qed

theorem t2 : ⊢ T := by exact truth
qed
```

Where:

- `<name>` is the theorem name.
- `[(binder...)]` currently supports zero or more theorem-header binders.
- `<goal>` is a sequent.
- `<steps>` are the proof steps, written either in single-line sequential form or in newline-separated
  block form.

For compatibility with existing examples, a single-theorem file may omit the trailing `qed`. In a
multi-theorem file, each preceding theorem must be followed by `qed` before the next top-level
`theorem`.

## Theorem header

### Theorem name

Minimal example:

```text
theorem truth_file : ⊢ T := by exact truth
```

### Theorem-header binders

The current shipped binder form is:

```text
(x : bool)
```

For example:

```text
theorem id_bool (x : bool) : ⊢ x -> x := by
  intro h
  exact h
qed
```

The safest file-first usage in the current documentation and examples is to start with `bool`
binders.

### Currently supported quantified goals

A raw `forall` theorem goal like the following is now accepted as goal-only sugar:

```text
theorem quant_raw_intro_ok : ⊢ forall (x : bool), x -> x := by
  intro h
  exact h
qed
```

The parenthesized form is also accepted:

```text
theorem quant_raw_intro_paren_ok : ⊢ (forall (x : bool), x -> x) := by
  intro h
  exact h
qed
```

In other words:

- Theorem-header binders `(x : bool)` and raw `forall` / `∀` theorem goals are both part of the
  currently shipped quantifier-facing user syntax.
- Raw `forall (x : A), body` / `∀ (x : A), body` is accepted only at the theorem-script goal /
  `parse_goal` entry points; it is not term-level syntax.
- The raw `forall` path is currently only goal sugar; it follows the same lowering / replay / CLI
  diagnostics contract and introduces no new kernel quantifier authority.

## Goal shape

The current shipped surface uses sequent goals:

```text
⊢ goal
A ⊢ B
A, B ⊢ goal
```

The minimal runnable examples in the README and `examples/` mainly use:

- `⊢ T`
- `⊢ x -> x`
- `⊢ x -> x ∧ x`
- `⊢ x -> x ∨ x`

For first-time CLI users, it is safest to start with state-free examples using `T`, `F`, and
theorem-header binders.

## Proof steps

The current shipped steps are only these:

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`
- `hole`

### `intro`

```text
intro h
```

When the current goal is `A -> B`, introduces a local hypothesis and continues by proving the
consequent.

### `exact`

```text
exact h
exact truth
```

Closes the current goal directly.

### `apply`

```text
apply and_elim_l
```

Applies an implication-backed theorem or a local implication hypothesis to the current goal,
producing new subgoals.

### `assumption`

```text
assumption
```

Searches the current local hypotheses for evidence that matches the current goal.

### `split`

Sequential form:

```text
split
```

Structured branch form:

```text
split { exact h } { exact h }
```

### `left` / `right`

Sequential form:

```text
left
right
```

Structured branch form:

```text
left { exact h }
right { right { hole h1 } }
```

### `hole`

```text
hole
hole h1
```

`hole` does not fake success; it currently returns a structured unfinished result.

## Sequential blocks and structured branch blocks

`<steps>` can currently be written on a single line:

```text
theorem t1 (x : bool) : ⊢ x -> x := by intro h; exact h
```

or as a multi-line block:

```text
theorem t1 (x : bool) : ⊢ x -> x := by
  intro h
  exact h
qed
```

When steps need explicit branching, a minimal structured branch block is currently supported:

```text
theorem demo_and (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
qed
```

An example closer to classical propositional logic:

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
qed
```

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
qed
```

## Most important current limitations

- The current `src/cmd` workflow is file-first; a single-theorem file may omit the trailing `qed`,
  and a multi-theorem file uses `qed` as a separator.
- Directly runnable public examples should preferably use the existing scripts in `examples/`.
- Theorem-header binders are shipped; raw `forall` theorem goals are supported as goal-only sugar,
  while term-level forms are still unsupported.
- Unsupported paths must fail closed and never fake theorem success.
- `hole` returns unfinished, not theorem success.

## Output shape

Current CLI output falls into three categories:

- Success: by default, one line `ok <theorem_name>` per theorem; with `-d`, the output is
  `ok <theorem_name>: <conclusion_summary>`
- Failure: `error[kind] ...`
- Unfinished: `warning[unfinished] ...`; it produces no theorem authority, but checking continues
  with the following theorems.

The `--` in `moon run src/cmd -- -d --no-warn <file>` belongs only to `moon run` argument
forwarding; a standalone executable does not need it, so run `qed-cmd -d --no-warn <file>` directly.

See [User manual](manual.md) for the complete failure fields, unfinished fields, and stable examples.
