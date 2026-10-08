# User manual

- Status: active
- Audience: users, contributors, implementers
- Authority: user guide + implementation contract; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ) and current code/tests
- Scope: current shipped behavior, beginner-facing usage, trust boundary, support matrix, and stable examples
- Last reviewed: 2026-10-08

This document is both the current QED user manual and its implementation contract.

It follows the MoonBit and Lean code in the current repository workspace and answers three questions:

- how an ordinary user actually writes and runs a small proof today;
- what is actually implemented today;
- what the surrounding tooling is currently allowed and not allowed to do.

## For readers new to HOL

If you have not used proof assistants such as HOL, Lean, HOL Light, or Isabelle before, the following
intuitions are enough to understand the subset QED currently ships:

- A "proof" here is not a natural-language paragraph but a script that the kernel checks.
- The goals currently shipped are mainly a minimal propositional-logic subset, plus a small amount of
  equality and theorem replay.
- `⊢ goal` means "prove `goal` with no premises".
- `A, B ⊢ goal` means "prove `goal` under the hypotheses `A` and `B`".
- Intuitively, read `T` as "the always-true proposition" and `F` as "the false proposition".
- `A -> B` means "given `A`, you can derive `B`".
- `A ∧ B` means "prove both `A` and `B`".
- `A ∨ B` means "proving one side of `A` or `B` suffices, but you must explicitly choose left or right".
- `P = Q` denotes equality; the currently shipped subset also supports a small amount of
  equality-related theorem replay.

Roughly, a theorem script is currently a sequence of "goal-directed proof steps":

- `intro h`: if the current goal is `A -> B`, it becomes "add a local hypothesis `A` named `h` and
  continue proving `B`".
- `exact h`: if `h` is already direct evidence for the current goal, it closes the goal immediately.
- `assumption`: searches the current local hypotheses for evidence that matches the goal.
- `apply th`: applies an implication theorem or a local implication hypothesis to the current goal,
  producing new subgoals.
- `split`: when the goal is `A ∧ B`, splits it into two subgoals.
- `left` / `right`: when the goal is `A ∨ B`, explicitly chooses to prove the left or the right branch.
- `hole`: admits that this point is not proved yet; the system returns a structured unfinished result
  instead of faking success.

These intuitions are enough to start reading the first few examples in this user manual; the full
boundaries, rule names, and support matrix come later.

## Getting started order

We recommend starting in this order:

1. Run `moon build` and `moon test` first to confirm the workspace itself is green.
2. Use `src/cmd` to run a fully state-free theorem file and get familiar with the input and output format.
3. Then try examples with theorem-header binders to understand "how local variables enter the proof context".
4. Finally, read the support matrix, failure matrix, and implementation contract to understand which
   capabilities are shipped and which are not.

## Quick start

### 1. Build

```bash
moon build
moon test
```

### 2. Run your first proof file

Create a file in the repository root, for example `truth_file.qed`:

```text
theorem truth_file : ⊢ T := by exact truth
```

Then run:

```bash
moon run src/cmd truth_file.qed
```

A successful run currently prints:

```text
ok truth_file
```

To see the full conclusion summary, add `-d`:

```bash
moon run src/cmd -- -d truth_file.qed
```

When launching through `moon run`, `--` is the MoonBit runner's argument separator; without it, `moon`
parses `-d` itself and the QED CLI never receives the flag. Once compiled to a standalone executable,
you can write directly:

```bash
qed-cmd -d truth_file.qed
```

A theorem that contains `hole` is reported as `warning[unfinished]`; it does not construct a theorem
and does not enter the subsequent kernel state. By default a warning makes the overall exit code
non-zero; to allow warnings as long as there is no real error, use `--no-warn`:

```bash
moon run src/cmd -- --no-warn file.qed
qed-cmd --no-warn file.qed
```

This example is a good first step because it depends on no extra free constants and does not require you
to understand binders, branches, or the theorem inventory in advance.

### 3. Second example: the minimal "assume and return it unchanged"

```text
theorem id_bool (x : bool) : ⊢ x -> x := by
  intro h
  exact h
```

There are two layers to note here:

- `(x : bool)` is a theorem header binder. It introduces a local variable `x` into the theorem goal.
- `intro h` turns the goal `x -> x` into "assume `h : x`, prove `x`".
- `exact h` states that the local hypothesis `h` is now direct evidence for the current goal.

This is also currently the script best suited to readers without a HOL background: it only shows "goal
rewriting" and "closing with evidence", and depends on no extra theorem names.

### 4. Third example: constructing a conjunction

```text
theorem dup_bool (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
```

This example shows that:

- the goal `x ∧ x` requires proving the left and right sides separately;
- `split` produces two branches;
- each branch can again be closed with `exact h`.

If you prefer the sequential style, you can also `split` first and then complete the two subgoals in
order; for beginners, however, the structured branch blocks of `split { ... } { ... }` are more intuitive.

### 5. Fourth example: a classic conjunction commutativity theorem

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
```

This script shows one of the most classic propositional-logic patterns: building `q ∧ p` back from `p ∧ q`.
It looks more like a real mathematical statement than `x -> x`, yet it stays entirely within the
currently shipped syntax and capabilities.

### 6. Fifth example: seeing an honest failure

The following script is deliberately wrong:

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
```

It does not return theorem success; it returns a structured failure. The reason is that the current
left-branch goal is actually `x`, but `truth` can only directly close `T`.

For the current canonical output example, see `manual:quantifier_failure_matrix` later in this document.

### 7. Sixth example: seeing an unfinished proof

```text
theorem unfinished_branch (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by
  intro h
  right { right { hole h1 } }
```

Here `hole h1` means "I know one proof obligation is still missing, but I am leaving it empty for now".
QED honestly returns an unfinished result and keeps:

- the theorem name;
- the step index;
- the branch path;
- the current goal;
- the current locals;
- the hole name.

This matters for interactive frontends, IDE diagnostics, and later proof authoring, but it is not a theorem.

## The current input model from a user's perspective

If you mainly want to look up "exactly what syntax the command line accepts", see [Syntax guide](syntax.md) first.
This section keeps a shorter summary of the input model; for the support matrix, failure semantics, and
implementation contract, this document remains authoritative.

### What a theorem script looks like

The currently shipped theorem script has the shape:

```text
theorem <name> [(binder...)] : <goal> := by <steps>
```

where:

- `<name>` is the theorem name.
- `[(binder...)]` currently supports zero or more theorem-header binders of the form `(x : bool)`.
- `<goal>` is a sequent, for example `⊢ T`, `P ⊢ P`, `⊢ x -> x ∧ x`.
- `<steps>` can be written sequentially on one line, as a newline-separated block, or with a minimal
  structured branch block after `split` / `left` / `right`; this branch syntax is accepted by the parser
  and its execution is orchestrated by the prover.

### The most important current limitations

If you are using `src/cmd` for the first time, these points matter most:

- When running scripts directly file-first, start with state-free examples such as `T`, `F`, and the
  theorem-header binder `(x : bool)`.
- Many examples in the docs that use `P`, `Q`, and the like exist to illustrate the support matrix; in
  the tests they are first placed into the corresponding kernel state before the prover is called.
- Theorem-header binders are already a shipped surface; raw `forall (x : A), body` / `∀ (x : A), body`
  is now accepted as goal-only sugar, but it is still not term-level syntax.
- The only supported steps are `intro`, `exact`, `apply`, `assumption`, `split`, `left`, `right`, `hole`.
- Unsupported paths fail closed and never fake theorem success.

### Command-line workflow

The currently shipped `cmd` entry point is:

```bash
moon run src/cmd <file>
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

The input is a theorem-script file; a single-theorem file may omit the trailing `qed`, and a
multi-theorem file separates theorems with lowercase `qed`. There are three kinds of output:

- Success: by default one line `ok <theorem_name>` per theorem; with `-d` the output is
  `ok <theorem_name>: <conclusion_summary>`
- Failure: `error[kind] ...`, with `step`, `branch`, `goal`, `locals` when relevant
- Unfinished: `warning[unfinished] ...`, with context such as `hole`, `goal`, `locals`; it produces no
  theorem authority, but checking continues with the following theorems

Under `moon run`, passing `-d` / `--no-warn` requires the `--` separator; a standalone executable can use
`qed-cmd -d --no-warn <file>` directly.

This means it is no longer a black-box CLI with "only success and failure", but one that exposes the key
diagnostics about the current proof state.

## Source-of-truth hierarchy

QED currently follows the documentation hierarchy defined in [Documentation governance](governance.md). For the implementation
contract, the relevant order is:

1. [QED formal specification](../attachments/qed_formal_spec.typ) is the only normative source, and [`doc/attachments/qed_formal_spec.typ`](../attachments/qed_formal_spec.typ)
   is its source file.
2. The current code and regression tests determine the "actual shipped state".
3. This document and [Specification conformance](conformance.md) describe the current implementation contract and engineering conformance.
4. `README.md` and `CHANGELOG.md` are external summaries only and rank no higher than the above.
5. `research/` only records unshipped design research and is not a product contract.

If the implementation and the documentation conflict, first establish the actual state from code + tests,
then update the documentation.
If the implementation and the paper's specification conflict, the paper's specification still prevails.

## Trust boundary

QED uses a kernel-first architecture. The only theorem-construction boundary is `src/kernel`.

- `kernel` owns types, terms, theorem objects, signature state, primitive rules, and the
  `DefOK` / `TypeDefOK` / `SpecOK` gates.
- `logic` may only be a thin wrapper over the checked kernel API, definition/unfold helpers,
  replay helpers, and a non-authoritative theorem-reference organization layer; it must not introduce new
  primitive rule authority.
- `elab` owns one-shot resolution, resolved/core typing, and lowering; it does not define new logic.
- `parser` owns textual syntax, normalization, parser-owned lowering results, and local environment
  management; it must not silently change connector semantics or scope rules, and must not directly own
  tactics execution objects.
- `tactics` owns goal-state transformation and replay orchestration; it owns no theorem authority and does
  not interpret the structured branch syntax of theorem scripts.
- `prover` is only the orchestration entry point over parser + tactics + kernel; on the supported subset
  it can return a trusted `Thm`, and unsupported paths must keep failing closed; it may explicitly bridge
  parser lowering results to `tactics.Goal` and schedules the scripts of structured branch blocks, but it
  never pushes tactics objects back into the parser.
- The repository no longer keeps the old phase0/demo `cmd` path; the current `src/cmd` is a file-first,
  non-authoritative entry point and still must not become a second proof kernel.

`Thm` remains an opaque type at the package boundary; external callers must interact through the
checked/stateful interfaces.

Each package also has an API reference, a design note and a tutorial; the [manual overview](index.md)
lists them. The [kernel design](design/kernel.md) explains why soundness reduces to the kernel.

## Implemented kernel

The parts of the kernel that are currently stable include:

- Type core: `bool`, `ind`, `fun(a, b)`, general `TyApp`, and type variables.
- Term boundary: named `Term` externally, typed `DbTerm` internally to run the alpha-invariant rule core.
- Checked primitive rule interfaces:
  - `refl_checked`
  - `assume_checked`
  - `trans_checked`
  - `mk_comb_rule_checked`
  - `abs_rule_checked`
  - `beta_rule_checked`
  - `eq_mp_checked`
  - `deduct_antisym_rule_checked`
  - `inst_type`
  - `inst_checked`
- Theorem admissibility checks:
  - theorem const-id bindings must agree with the current state;
  - constant instantiation must satisfy the principal schema instance relation;
  - definitional theorems must pass `def_inst_coherent`;
  - every type occurring in a theorem / sentence must belong to the current `Sigma_t`;
  - type substitutions must pass the admissibility gate.
- Scoped signature state:
  - `empty_kernel_state`
  - `ks_push_scope`
  - `ks_pop_scope`
  - `ks_add_const`
  - `ks_mk_const`
  - `ks_mk_const_instance`
- Extension gates:
  - `ks_define_const`
  - `ks_define_const_thm`
  - `ks_register_type_definition`
  - `ks_specify_const`
- Key constraints already covered by the extension discipline:
  - def-head monotonicity
  - scope push/pop discipline
  - ghost type variable rejection
  - definition closure / cycle rejection
  - typedef witness validity
  - specification witness validity
- Audit and replay helper interfaces:
  - `ks_extension_cert_count`
  - `ks_extension_cert_at`
  - `ks_conservative_replay_ok`

These audit objects serve only observability and conservativity regression; they are not new proof objects.

## Frontend contracts

### Resolved elaboration

The frontend currently keeps three term representations:

1. named `Term`
2. resolved `RTerm`
3. typed `DbTerm`

`RTerm` is not meant to replace kernel terms; it freezes the result of one-shot resolution. Currently
`ResolvedConst` records:

- `name`
- `const_id`
- `inst_ty`
- `schema_ty`

This means a constant is bound to its kernel identity at elaboration time; later `push` /
`pop` / shadowing only affects future name resolution and never writes back into existing resolved objects.

The current resolved/core typing contract is:

- `RVar` matches only against the current local context and its explicit type;
- `RConst` must still correspond to the same `const_id` and `schema_ty`;
- `inst_ty` must still satisfy the principal schema instance relation;
- if a scope change makes the frozen identity no longer acceptable, typing must fail closed instead of
  silently looking up a constant with the same name again.

### Parser

The parser is currently the single entry point for "textual syntax -> AST -> resolved elaboration ->
parser-owned lowered object".

The stable contract includes:

- Name resolution order is always `local > const`.
- `parse_goal` / `lower_syn_goal_with_env` currently return a parser-owned `ParsedGoal`;
  tactics execution objects are constructed only when the upper layer bridges.
- Input first goes through `normalize_parser_input`:
  - `\not` / `\and` / `\or` / `\imp` are normalized to their canonical forms;
  - `|-` is normalized to `⊢`;
  - basic redundant whitespace is collapsed;
  - this phase does no AST-level pretty printing.
- `ParseError.offset` still maps back to the user's original input, not to coordinates in the normalized string.
- The canonical display syntax is primarily Unicode:
  - term: `¬`, `∧`, `∨`, `->`, `=`
  - goal: `⊢`
- Compatibility input is still accepted:
  - `\not`, `\and`, `\or`, `\imp`
  - `|-`
- The old ASCII connective spellings `/\` and `\/` are no longer accepted
- The raw theorem script entry point currently supports:
  - zero or more `(name : type)` binders in the theorem header
  - single-line `theorem <name> : <goal> := by <step>; <step>; ...`
  - block-style `theorem <name> : <goal> := by` followed by a newline-separated sequential list of steps
  - the `hole` / `hole <name>` unfinished-proof step
- The theorem-script AST currently keeps raw-source spans for theorem header binders, the theorem goal,
  and each step; these positions still refer to the user's original input and are never silently
  rewritten to normalized coordinates.
- Theorem header binders are currently a shipped quantifier-facing surface:
  they introduce binder names into goal lowering, proof-state locals, and cmd diagnostics;
  but they grant no new theorem authority to tactic/prover.
- `forall (x : A), body` / `∀ (x : A), body` is currently accepted as goal-only sugar;
  but it is still not term-level syntax.

The parser also currently exposes:

- `parse_let`
- `parse_def_function`

They are currently a supported parser-side utility surface: covered by tests and callable on their own,
they handle local environment extension and closure-style function definition parsing; but they are not
part of the main theorem-script syntax and do not extend theorem-construction authority.

### Surface connectors

`¬` / `->` / `∧` / `∨` are currently all surface connectors, not kernel primitive logic.

The common contract includes:

- during lowering, parser/bridge generate proposition terms through the basis-backed builders of the `logic` layer;
- `prop_mk_not` / `prop_mk_imp` / `prop_mk_and` / `prop_mk_or` must return `LogicError` on non-`bool`
  input and must not crash;
- the trusted semantic basis of these connectors comes from kernel terms, equality `=`, choice `@`, and
  checked primitive rules;
- they must not be treated as additional rule authority in `tactics`, `prover`, or a future `cmd`;
- the parser no longer requires an ordinary constant of the same name to exist in the state before it can
  parse these connectors;
- `logic.install_prop_prelude` counts as an idempotent success only when the existing constant of the same
  name already has the canonical definition theorem; a placeholder constant with the same name and type
  but no canonical definition must be rejected;
- `prop_dest_not` / `prop_dest_imp` / `prop_dest_and` / `prop_dest_or` currently use
  state-backed trusted recognition: they accept only canonical basis terms or connector constants that
  have the canonical definition theorem in the current state.

### Logic helpers

`src/logic` currently serves as the foundation layer for broadening theorem replay in the future; its
stable visible capabilities include:

- Proposition basis term builders:
  - `prop_mk_not`
  - `prop_mk_imp`
  - `prop_mk_and`
  - `prop_mk_or`
- Proposition destructors:
  - `prop_dest_not`
  - `prop_dest_imp`
  - `prop_dest_and`
  - `prop_dest_or`
- Connector definition theorem / unfolding helpers:
  - `logic_prop_def_imp`
  - `logic_prop_def_not`
  - `logic_prop_def_and`
  - `logic_prop_def_or`
  - `logic_prop_unfold_head`
  - `logic_prop_unfold_imp`
  - `logic_prop_unfold_not`
  - `logic_prop_unfold_and`
  - `logic_prop_unfold_or`
- Equality lifting / normalization helpers:
  - `logic_apply_fun_eq`
  - `logic_apply_fun_eq2`
  - `logic_beta_normalize_eq`
  - `logic_eq_sym`
  - `logic_eq_mp_bool`
- Proposition replay helpers:
  - `logic_prop_close_hypothesis`
  - `logic_prop_ensure_sequent`
  - `logic_prop_discharge_imp_prefix`
  - `logic_prop_replay_imp_elim_backward`
  - `logic_prop_merge_conjunction`
  - `logic_prop_or_wrap_left`
  - `logic_prop_or_wrap_right`
- Theorem catalog / resolver helpers:
  - `logic_prop_theorem_count`
  - `logic_prop_theorem_at`
  - `logic_prop_theorem_entry`
  - `logic_prop_resolve_exact_theorem`
  - `logic_prop_resolve_apply_theorem`

The goal of these helpers is to keep the replay paths of proof synthesis and the theorem catalog on an
explicit kernel-checked path, instead of silently adding semantic shortcuts in the frontend.

## Proof scripting status

For **supported tactics and prelude rules**, the proof scripting layer currently constructs a kernel
`Thm` through `logic` replay; unsupported input still fails closed and never fakes a theorem.

The objects and entry points already implemented include:

- `Goal`
- `ProofState`
- `ps_init`
- `ps_current_goal`
- `ps_goal_count`
- `ps_apply`
- `ps_apply_script`
- `ps_qed`
- `prove_theorem_script`
- `prove_theorem_script_detailed`
- `prove_theorem_script_with_diagnostics`

The only currently supported steps are:

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`
- `hole`

`exact` / `apply` are no longer limited to local-name-only operations.

- `exact` currently works with witness semantics: it first resolves a local hypothesis witness; on a
  local miss, it resolves an exact-capable theorem entry and requires it to directly witness the current sequent.
- `apply` first resolves a local implication; on a local miss, it can resolve a small set of stable
  propositional theorem names or context-derived propositional theorems.
- The current exact-capable theorem names are:
  - `imp_refl`
  - `truth`
  - `and_elim_l`
  - `and_elim_r`
  - `and_intro`
  - `not_elim`
  - `ex_falso`
  - `imp_elim`
  - `eq_refl`
  - `eq_sym`
  - `eq_mp`
- The current implication-backed apply names are:
  - `and_elim_l`
  - `and_elim_r`
  - `or_intro_l`
  - `or_intro_r`
  - `eq_sym`
- `or_intro_l` / `or_intro_r` currently stay `apply`-only; they need backward replay to construct their
  premises, so they are not direct witnesses of the current goal.
- The theorem-name inventory is now exposed in one place by `logic` and consumed jointly by `tactics`,
  `prover`, tests, and documentation; no second set of theorem-name semantics may again be maintained
  piecemeal inside `ProofState`.
- All these names must replay to existing kernel-checked `Thm`s; they are not new proof authority.
- `exact` never implicitly degrades into `apply`; names that first need new subgoals and then completion
  through backward replay do not belong to `exact`.
- Local `exact h` currently accepts only an active hypothesis alias; once a name hits a local, it never
  falls back to a theorem entry with the same name.
- `apply` accepts only implication theorems; for direct-close theorem names such as `truth` / `not_elim` /
  `ex_falso` it must fail honestly.

The current semantic boundary should be understood as follows:

- `tactics` transforms the stack of unsolved goals and organizes the evidence needed for replay;
- `prover` parses the script, sets up the goal, and executes the steps;
- `prove_theorem_script_detailed` / `prove_theorem_script_with_diagnostics`
  currently keep, on honest failure, the theorem name, step index, current goal, local hypotheses,
  branch path, and the raw-source location of the goal/step; these diagnostic objects are engineering aids, not new proof objects;
- if a theorem script contains `hole`, a structured unfinished-proof result is currently returned,
  keeping the theorem name, step index, current goal, local hypotheses, branch path,
  hole name, and source location; an unfinished-proof result is not a theorem;
- `ps_qed` returns the final `Thm` only when replay succeeds and matches the root goal's sequent;
- `ps_qed` currently validates the final theorem with strict normalized sequent matching:
  it first applies proposition beta normalization uniformly, then checks alpha-invariant agreement of the
  hypothesis set and the conclusion; the old loose shape match is no longer accepted.
- Unsupported paths keep returning honest failures such as `ProofSynthesisUnavailable`, `Logic`, or tactic errors.

## Current support matrix

### Shipped now

- checked kernel + scoped signature + gate discipline
- resolved elaboration boundary
- parser normalize/raw-offset/theorem-script raw parsing, including sequential
  block bodies, structured branch blocks, theorem-header binders, the hole step,
  and raw binder/goal/step spans
- a quantifier-facing script surface driven by theorem-header binders, with the corresponding
  prover/cmd goal, locals, branch, and unfinished-proof summaries
- parser-side utility APIs `parse_let` / `parse_def_function`
- proposition prelude definition theorems + unfold helpers
- supported propositional tactic replay to kernel `Thm`
- unfinished-proof reporting for theorem scripts containing holes
- file-first `cmd` workflow for theorem-script files with optional `qed`
  terminators and multiple theorem blocks

### Explicitly not shipped

- richer theorem blocks
- promoted rewrite/simplify tactic or command surface
- kernel metavariables / hole completion authority
- dictionary passing / typeclass frontend
- arbitrary theorem-environment references
- arbitrary script completeness

### Current extension contract

- the theorem-name inventory, corpus, mapping matrix, and docs use the same set of shipped anchors;
- nested proof blocks continue to be organized through the current checked replay boundary;
- hole / unfinished-proof remains a frontend contract, not kernel metavariable authority;
- theorem-header binders remain part of the currently shipped quantifier-facing syntax and stay in sync
  with the corpus / matrix;
- a new public example must enter the regression tests first, and only then the documentation anchors.

### Stable theorem-name surface

| Surface | Current supported capability | Stable theorem names |
| --- | --- | --- |
| `exact` | local hypothesis witness, theorem entries with exact capability | `imp_refl`, `truth`, `and_elim_l`, `and_elim_r`, `and_intro`, `not_elim`, `ex_falso`, `imp_elim`, `eq_refl`, `eq_sym`, `eq_mp` |
| `apply` | local implication, implication-backed named theorem, implication-backed context theorem | `and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`, `eq_sym` |

The stable contract includes:

- `exact` consumes only the exact capability and never implicitly degrades into `apply`. This covers both
  direct-close entries and context-derived exact entries; local `exact h`
  must also interpret `h` as a direct witness of the current sequent, and `h` must still be an active
  hypothesis alias, not a shape-based guess or some other local artifact.
- `apply` consumes only the implication-backed capability; it never accepts a direct-close theorem
  name as an implication.
- Wrong-mode theorem usage keeps failing honestly; `exact or_intro_l` currently returns
  `GoalShapeMismatch`, local `exact h` also returns `GoalShapeMismatch` if `h` is not a direct witness of
  the current goal; `apply truth`, `apply ex_falso`, and `apply not_elim`
  must all currently return `ApplyMismatch`.
- Local name resolution still follows `local > theorem name`.

### M3c corpus / mapping matrix

The canonical corpus of the currently shipped subset uses "four kinds":

- Executable corpus:
  - `src/prover/prover_positive_corpus_test.mbt`
  - `src/prover/prover_negative_corpus_test.mbt`
  - the canonical unfinished-proof regressions in `src/prover/prover_test.mbt` /
    `src/cmd/cmd_corpus_wbtest.mbt`
  - the quantifier-facing binder / raw-`forall` canonical cases in `src/prover/corpus.mbt`,
    anchored jointly by `src/cmd/cmd_corpus_wbtest.mbt` and
    `src/prover/prover_mapping_matrix_test.mbt`
  - `src/prover/prover_mapping_matrix_test.mbt`
- Readable mapping:
  - the support matrix and example-source notes in this section

Here:

- `manual:runnable_examples` denotes the runnable theorem-script examples currently published;
- `manual:support_matrix` denotes the positive support-matrix cases currently published;
- `manual:failure_matrix` denotes the honest failure / negative examples currently published;
- `internal_only` denotes cases that still belong to the canonical corpus but are currently not placed
  directly into the documentation's example text.

| Corpus case | Visibility / anchor | Surface | Catalog / capability | Current contract |
| --- | --- | --- | --- | --- |
| `pos_intro_exact_identity` | `public_example` / `manual:runnable_examples` | `intro` + `exact h` | `local_fact` / `intro_exact` | Local hypothesis closes the goal directly |
| `pos_local_shadow_exact_named_theorem` | `public_example` / `manual:support_matrix` | `exact imp_refl` | `local_fact` / `mixed` | `local > theorem name` |
| `pos_exact_imp_refl` | `public_example` / `manual:support_matrix` | `exact imp_refl` | `direct_close` / `exact_named_direct_close` | direct-close theorem |
| `pos_exact_and_elim_l` | `public_example` / `manual:support_matrix` | `exact and_elim_l` | `context_derived` / `exact_context_derived` | Depends on a conjunction owner in the context |
| `pos_apply_and_elim_l` | `public_example` / `manual:runnable_examples` | `apply and_elim_l` | `implication_backed` / `apply_named_imp` | implication-backed context replay |
| `pos_apply_or_intro_l` | `public_example` / `manual:support_matrix` | `apply or_intro_l` | `implication_backed` / `apply_named_imp` | implication-backed goal-shape replay |
| `pos_split_conjunction` | `public_example` / `manual:support_matrix` | `split` | `structural_only` / `split` | Sequential structural goal orchestration |
| `pos_branch_split_conjunction` | `public_example` / `manual:support_matrix` | `split { ... } { ... }` | `structural_only` / `split` | Structured conjunction branch blocks |
| `pos_left_disjunction` | `public_example` / `manual:runnable_examples` | `left` | `structural_only` / `left` | Sequential branch selection on a disjunction goal |
| `pos_branch_left_disjunction` | `public_example` / `manual:runnable_examples` | `left { ... }` | `structural_only` / `left` | Structured disjunction branch block |
| `pos_exact_truth` | `public_example` / `manual:runnable_examples` | `exact truth` | `direct_close` / `exact_named_direct_close` | Closes a `T` goal directly |
| `pos_exact_ex_falso` | `public_example` / `manual:runnable_examples` | `exact ex_falso` | `context_derived` / `exact_context_derived` | Honestly closes any bool goal under hypothesis `F` |
| `pos_quant_seq_identity` | `public_example` / `manual:quantifier_examples` | `(x : bool)` binder + `intro` / `exact` | `quantifier_surface` / `quantifier_intro_exact` | Sequential quantifier surface driven by a theorem-header binder |
| `pos_quant_branch_split` | `public_example` / `manual:quantifier_examples` | `(x : bool)` binder + `split { ... } { ... }` | `quantifier_surface` / `quantifier_split_branch` | Compatibility positive case for binder + branch block |
| `pos_quant_forall_seq_identity` | `public_example` / `manual:quantifier_examples` | `forall (x : bool), ...` + `intro` / `exact` | `quantifier_surface` / `quantifier_forall_intro_exact` | Sequential quantifier surface driven by raw theorem-goal sugar |
| `pos_quant_forall_branch_split` | `public_example` / `manual:quantifier_examples` | `forall (x : bool), ...` + `split { ... } { ... }` | `quantifier_surface` / `quantifier_forall_split_branch` | Compatibility positive case for raw theorem-goal sugar + branch block |
| `neg_exact_or_intro_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `exact or_intro_l` | apply-only theorem misuse in exact mode | `GoalShapeMismatch` |
| `neg_apply_truth_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | direct-close theorem misuse | `ApplyMismatch` |
| `neg_local_shadow_truth_is_not_implication` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | local shadow failure | Still resolves the local first, then fails honestly |
| `neg_exact_context_missing` | `public_failure_example` / `manual:failure_matrix` | `exact and_elim_l` | context-derived missing owner | `GoalShapeMismatch` |
| `neg_non_bool_connector_rejected` | `public_failure_example` / `manual:failure_matrix` | `f ∧ Q` | frontend boundary reject | Non-`bool` connector fails closed |
| `neg_quant_branch_goal_mismatch` | `public_failure_example` / `manual:quantifier_failure_matrix` | `(x : bool)` binder + `left { exact truth }` | `quantifier_surface` / `quantifier_goal_shape_mismatch` | Binder locals are kept and branch blame is stable |
| `neg_quant_forall_branch_goal_mismatch` | `public_failure_example` / `manual:quantifier_failure_matrix` | `forall (x : bool), ...` + `left { exact truth }` | `quantifier_surface` / `quantifier_forall_goal_shape_mismatch` | Locals and branch blame are stable under raw theorem-goal sugar |
| `unf_quant_nested_branch_hole` | `public_example` / `manual:quantifier_unfinished_examples` | `(x : bool)` binder + nested `hole` | `unfinished_proof` / `quantifier_unfinished_hole` | Binder locals, nested branch path, and unfinished rendering |
| `unf_quant_forall_nested_branch_hole` | `public_example` / `manual:quantifier_unfinished_examples` | `forall (x : bool), ...` + nested `hole` | `unfinished_proof` / `quantifier_forall_unfinished_hole` | Locals, nested branch path, and unfinished rendering under raw theorem-goal sugar |

### Runnable theorem-script examples

The following scripts are all **theorem-script examples that actually exist in the regression corpus**,
not planned capabilities.

But two things must be distinguished:

- "runnable in tests / a pre-populated state";
- "runnable by the user directly through `moon run src/cmd <file>`".

To see the full conclusion summary of a successful theorem, use
`moon run src/cmd -- -d <file>` when going through `moon run`; once compiled to a standalone executable, use
`qed-cmd -d <file>`.

Only state-free scripts that depend on no extra free constants are suitable as first file-first examples.
Users new to this project should look first at `truth_file`, `id_bool`, and `dup_bool` earlier in this manual.

The `prelude/` directory at the repository root additionally collects a set of theorem assets that can
currently be run directly, corresponding to the layer adjacent to HOL Light bool-core; these files serve
as runnable library-style examples, but are not yet wired into the current theorem-name inventory / resolver.

The following examples mainly serve to publicly document the coverage of the currently shipped
theorem-script subset:

```text
theorem t1 : ⊢ P -> P := by intro h; exact h
theorem t2 : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h
theorem t3 : ⊢ P -> P ∨ Q := by intro h; left; exact h
theorem t4 : P ⊢ P ∨ Q := by left { assumption }
theorem t5 : ⊢ T := by exact truth
theorem t6 : F ⊢ Q := by exact ex_falso
```

These examples are currently covered by the positive regressions in `src/prover/prover_test.mbt`,
`src/prover/prover_positive_corpus_test.mbt`, and `src/tactics/proof_state_test.mbt`; when adding or
changing a public example, first make the corresponding test facts hold, then update the documentation.

The current mapping between the public runnable examples and canonical case ids is:

| Example | Corpus case | Current support path |
| --- | --- | --- |
| `t1` | `pos_intro_exact_identity` | local fact / `intro_exact` |
| `t2` | `pos_apply_and_elim_l` | implication-backed / `apply_named_imp` |
| `t3` | `pos_left_disjunction` | structural-only / `left` |
| `t4` | `pos_branch_left_disjunction` | structural-only / `left` structured branch |
| `t5` | `pos_exact_truth` | direct-close / `exact_named_direct_close` |
| `t6` | `pos_exact_ex_falso` | context-derived / `exact_context_derived` |

`src/prover/prover_mapping_matrix_test.mbt` is currently the single test anchor between corpus cases,
capability labels, and documentation anchors; to add, change, or remove a public example in the
documentation, first update the corresponding canonical case, then update the mapping matrix and this
document accordingly.

### Quantifier-facing examples

The currently shipped quantifier surface has two user paths: theorem-header binders and raw `forall`
theorem goal sugar. The two groups of scripts below are both anchored by regression tests and the mapping matrix:

```text
theorem q1 (x : bool) : ⊢ x -> x := by intro h; exact h
theorem q2 (x : bool) : ⊢ x -> x ∧ x := by intro h; split { exact h } { exact h }
theorem qbad (x : bool) : ⊢ x -> x ∨ x := by intro h; left { exact truth }
theorem qunf (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

```text
theorem qf1 : ⊢ forall (x : bool), x -> x := by intro h; exact h
theorem qf2 : ⊢ forall (x : bool), x -> x ∧ x := by intro h; split { exact h } { exact h }
theorem qfbad : ⊢ forall (x : bool), x -> x ∨ x := by intro h; left { exact truth }
theorem qfunf : ⊢ forall (x : bool), x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

The mapping between these examples and canonical case ids is:

| Example | Corpus case | Current support path |
| --- | --- | --- |
| `q1` | `pos_quant_seq_identity` | quantifier surface / `quantifier_intro_exact` |
| `q2` | `pos_quant_branch_split` | quantifier surface / `quantifier_split_branch` |
| `qbad` | `neg_quant_branch_goal_mismatch` | quantifier failure / `quantifier_goal_shape_mismatch` |
| `qunf` | `unf_quant_nested_branch_hole` | quantifier unfinished / `quantifier_unfinished_hole` |
| `qf1` | `pos_quant_forall_seq_identity` | quantifier surface / `quantifier_forall_intro_exact` |
| `qf2` | `pos_quant_forall_branch_split` | quantifier surface / `quantifier_forall_split_branch` |
| `qfbad` | `neg_quant_forall_branch_goal_mismatch` | quantifier failure / `quantifier_forall_goal_shape_mismatch` |
| `qfunf` | `unf_quant_forall_nested_branch_hole` | quantifier unfinished / `quantifier_forall_unfinished_hole` |

In addition, forms with outer parentheses such as `⊢ (forall (x : bool), x -> x)` are currently also
accepted by the parser / prover; they follow the same raw-goal-sugar lowering path and simply do not
have a corpus case id of their own at present.

Readers without a HOL background can first understand these quantifier examples as follows:

- a theorem can first declare a local variable, such as `(x : bool)`;
- the goal that follows can then refer to this variable directly;
- a raw `forall` theorem goal is currently lowered to the same binder-oriented replay path.

The currently shipped quantifier frontend includes the binder entry and raw `forall` goal sugar; raw
`forall` is still not accepted in term positions.
This means users can now write and prove `forall` theorem goals, but it is still not general
term-level quantifier syntax, and it adds no kernel primitive quantifier authority.

### Unfinished-proof example

The current canonical unfinished-proof cases are also regression anchors and do not return a theorem:

```text
theorem unf_hole_intro : ⊢ T -> T := by intro h; hole h1
theorem unf_nested_branch_hole : ⊢ T ∨ (T ∨ T) := by right { right { hole h1 } }
```

These two cases are currently anchored jointly by `src/prover/prover_test.mbt`,
`src/prover/prover_mapping_matrix_test.mbt`, and `src/cmd/cmd_corpus_wbtest.mbt`; the former fixes the
root-level unfinished contract, the latter fixes the nested branch path and unfinished rendering.

The current quantifier-facing unfinished anchors cover both the binder path and the raw `forall` path:

```text
theorem unf_quant_nested_branch_hole (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
theorem unf_quant_forall_nested_branch_hole : ⊢ forall (x : bool), x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

They currently fix, respectively, the binder / raw-goal-sugar locals, the nested branch path, and the CLI
unfinished rendering.

## File-first workflow

The currently shipped `cmd` entry point is:

```bash
moon run src/cmd <file>
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

The current contract is:

- The input is a theorem-script file; a single-theorem file may omit the trailing `qed`, and a
  multi-theorem file separates theorems with lowercase `qed`;
- Success output is by default one line `ok <theorem_name>` per theorem; with `-d` the output is
  `ok <theorem_name>: <conclusion_summary>`;
- Failure output keeps `error[kind]`, the file path, and the theorem name, and on a tactic failure
  additionally reports:
  - `step`
  - `branch`
  - `goal`
  - `locals`
- If the script contains `hole`, the output is currently `warning[unfinished] ...`, with a summary of
  `step`, `branch`, `goal`, `locals`, `hole`, `message`; empty-value markers are stably `<none>` / `<root>`.
  A warning constructs no theorem, but the file-level runner keeps checking the following theorems;
- `--no-warn` only affects the exit code of warning-only files and does not hide the warning output;
- Under `moon run`, `--` only forwards the following arguments to the QED CLI; once compiled to a
  standalone executable, `qed-cmd -d --no-warn <file>` is enough and no `--` is needed.
- Theorem-header binder scripts and raw `forall` theorem-goal scripts share the same CLI
  contract; the `goal` / `locals` summaries are currently fixed as kernel-term strings, and branch/step
  blame and unfinished rendering are anchored jointly by `src/cmd/cmd_corpus_wbtest.mbt` and
  `src/cmd/cmd_wbtest.mbt`

The current minimal regression-checked example is:

```text
theorem truth_file : ⊢ T := by exact truth
```

If you only want to confirm that the environment and the command chain work, this is the best one to run first.

For a raw `forall` theorem-goal file, the current canonical CLI output example is:

```text
error[tactic] quant_forall_fail.qed (quant_forall_bad): GoalShapeMismatch(exact theorem does not directly close current goal)
step: 3
branch: 1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
```

```text
warning[unfinished] quant_forall_unfinished.qed (quant_forall_hole): proof contains an unfinished hole
theorem: quant_forall_hole
step: 4
branch: 1.1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
hole: h1
message: proof contains an unfinished hole
```

The theorem-header binder syntax currently uses the same set of fields and the same kind of blame
reporting; for the corresponding canonical corpus anchors, see `src/cmd/cmd_corpus_wbtest.mbt`.

## Current extension contract

The executable frontend may currently only be extended along the same set of shipped anchors:

- the theorem inventory, mode-aware resolver, corpus, mapping matrix, and docs keep a single source;
- structured branch blocks, as a prover-side script contract, keep reusing the existing checked replay boundary;
- hole / unfinished proof remains a frontend-only contract and does not enter kernel metavariable authority;
- theorem-header binders remain part of the currently shipped quantifier-facing user syntax;
- raw `forall` theorem goals remain supported as goal-only sugar and must not be documented as term-level syntax;
- the file-first workflow keeps reusing the same corpus / mapping matrix and does not fork a second set of semantics.

## Validation gate

Contributors should currently use the following gate to check that the implementation and the documentation agree:

```bash
moon build
moon test
cd formal_verification
lake build
```

If `.mbti` changes are involved or a merge is being prepared, also run:

```bash
moon info
moon fmt
moon test
```

Local check results:

- 2026-10-08, MoonBit `moonc` v0.10.14: `moon check --target all` reports no warnings and `moon test`
  passes (357 tests) on the `wasm`, `wasm-gc`, `js` and `native` targets
- 2026-04-05: `lake build` passes; `formal_verification/` has not changed since

For paper alignment, the code/test mapping, and the checklist for the surrounding tooling, read [Specification conformance](conformance.md).
