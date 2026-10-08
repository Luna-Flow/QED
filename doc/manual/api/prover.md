# prover API

## Purpose

The `prover` package (`Luna-Flow/QED/prover`) runs theorem scripts. It parses a script or a file of scripts, installs the propositional prelude if asked, lowers each goal, runs the steps with the `tactics` package (scheduling `{ ... }` branch blocks itself), and returns either a kernel theorem, a structured failure, or an unfinished-proof report for a script with a `hole`. It also publishes the regression corpus that ties the [user manual](../manual.md) to the tests.

The package orchestrates and reports; it holds no logical authority. The [prover design](../design/prover.md) explains the result model, and the [prover tutorial](../tutorial/prover.md) runs scripts from MoonBit.

## Importing

Add the package to your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/QED/prover",
  "Luna-Flow/QED/kernel",
}
```

The examples on this page are blackbox tests. They refer to this package as `@prover` and also use `@kernel`, so they import both packages.

## Options

### `ProverOptions`, `default_prover_options` and `prover_options`

`ProverOptions` has one switch: whether to install the propositional prelude into the state before running. `default_prover_options()` turns it on; `prover_options(b)` sets it explicitly.

```mbti
pub struct ProverOptions {
  auto_install_prelude : Bool
}

pub fn default_prover_options() -> ProverOptions
pub fn prover_options(Bool) -> ProverOptions
```

Without the prelude, `T`, `F` and the catalog theorems are unavailable unless the state already defines them.

## Running scripts

### `prove_theorem_script_detailed`

`prove_theorem_script_detailed(state, src, opts)` runs one theorem script and returns a three-way result.

```mbti
pub fn prove_theorem_script_detailed(@kernel.KernelState, String, ProverOptions) -> ProverRunResult
```

Header binders `(x : A)` become locals of the goal. The steps run in order; a step followed by branch blocks runs, and then each block runs on its subgoal in its own frame. The first failing step stops the script. A `hole` stops it as unfinished. If all steps succeed but goals remain, the result is a failure with `UnsolvedGoals`.

### `prove_theorem_script` and `prove_theorem_script_with_diagnostics`

These functions run one script and return the theorem and the state, or the failure or unfinished report as an error.

```mbti
pub fn prove_theorem_script(@kernel.KernelState, String, ProverOptions) -> Result[(@kernel.KernelState, @kernel.Thm), ProverScriptError]
pub fn prove_theorem_script_with_diagnostics(@kernel.KernelState, String, ProverOptions) -> Result[(@kernel.KernelState, @kernel.Thm), ProverScriptError]
```

The two functions currently behave identically; both carry the full diagnostics in `ProverScriptError`. The returned state is the state the proof ran in, with the prelude installed when requested; proved theorems are not added to it.

### `prove_theorem_file_results_detailed`

`prove_theorem_file_results_detailed(state, src, opts)` runs every theorem of a file whose theorems are separated by `qed` lines, and returns one result per theorem.

```mbti
pub fn prove_theorem_file_results_detailed(@kernel.KernelState, String, ProverOptions) -> ProverFileRunResult
```

A failing or unfinished theorem does not stop the file: later theorems are still checked. The whole file fails (`FileFailed`) only when it cannot be parsed or the prelude cannot be installed.

### `prove_theorem_file_detailed`

`prove_theorem_file_detailed` runs a file and summarises it as one result: the first failure if any, else the first unfinished theorem if any, else the last success.

```mbti
pub fn prove_theorem_file_detailed(@kernel.KernelState, String, ProverOptions) -> ProverRunResult
```

## Results

### `ProverRunResult`

`ProverRunResult` is the outcome of one script.

```mbti
pub enum ProverRunResult {
  Proved(ProverSuccess)
  Failed(ProverFailure)
  Unfinished(ProverUnfinished)
}
```

### `ProverSuccess`

`ProverSuccess` carries the theorem, the name of the script and the state it was proved in.

```mbti
pub struct ProverSuccess {
  state : @kernel.KernelState
  theorem_name : String
  thm : @kernel.Thm
}
```

### `ProverFailure`

`ProverFailure` describes where and why a script failed.

```mbti
pub struct ProverFailure {
  theorem_name : String?
  kind : ProverDiagnosticKind
  detail : String
  raw_offset : Int?
  goal_src : String?
  goal_span : @parser.SourceSpan?
  step_index : Int?
  branch_path : Array[Int]
  step_span : @parser.SourceSpan?
  step_src : String?
  current_goal : @tactics.Goal?
  local_hyps : Array[ProverLocalHyp]
  error : ProverError
}
```

`kind` and `error` say which layer failed; `detail` renders the error. The position fields locate the failure in the source: `raw_offset` for parse errors, the goal span for lowering errors, and the step index, branch path, step span and step text for tactic errors, together with the goal and locals at that point. Fields that do not apply are `None` or empty.

### `ProverUnfinished`

`ProverUnfinished` reports a script that reached a `hole`.

```mbti
pub struct ProverUnfinished {
  theorem_name : String
  detail : String
  raw_offset : Int?
  goal_src : String?
  goal_span : @parser.SourceSpan?
  step_index : Int?
  branch_path : Array[Int]
  step_span : @parser.SourceSpan?
  step_src : String?
  current_goal : @tactics.Goal
  local_hyps : Array[ProverLocalHyp]
  hole_name : String?
}
```

It has the same position fields as a failure, the goal the hole stands for (always present) and the hole's name if it has one. It is not a theorem.

### `ProverLocalHyp` and `prover_local_hyp`

`ProverLocalHyp` is a named local hypothesis in a report; `prover_local_hyp` builds one.

```mbti
pub struct ProverLocalHyp {
  name : String
  term : @kernel.Term
}

pub fn prover_local_hyp(String, @kernel.Term) -> ProverLocalHyp
```

### `prover_unfinished`

`prover_unfinished` builds an `Unfinished` result from its fields, in the order theorem name, goal source, goal span, step index, branch path, step span, step source, current goal, locals, hole name, detail and raw offset.

```mbti
pub fn prover_unfinished(String, String?, @parser.SourceSpan?, Int?, Array[Int], @parser.SourceSpan?, String?, @tactics.Goal, Array[ProverLocalHyp], String?, String, Int?) -> ProverRunResult
```

It exists for tests and renderers that need a fixed unfinished report.

### `ProverError` and `ProverDiagnosticKind`

`ProverError` wraps the error of the layer that failed; `ProverDiagnosticKind` names the layer.

```mbti
pub enum ProverError {
  Parse(@parser.ParseError)
  Bridge(@parser.ParseBridgeError)
  Tactic(@tactics.TacticExecError)
  Sig(@kernel.SigError)
  Logic(@kernel.LogicError)
}

pub enum ProverDiagnosticKind {
  Parse
  Bridge
  Tactic
  Sig
  Logic
}
```

### `ProverScriptError`

`ProverScriptError` is the error side of `prove_theorem_script`.

```mbti
pub enum ProverScriptError {
  Failure(ProverFailure)
  Unfinished(ProverUnfinished)
}
```

### `ProverFileRunResult`, `ProverFileReport` and `ProverFileItemResult`

A file run either fails as a whole or yields one item per theorem, in order.

```mbti
pub enum ProverFileRunResult {
  FileChecked(ProverFileReport)
  FileFailed(ProverFailure)
}

pub struct ProverFileReport {
  state : @kernel.KernelState
  items : Array[ProverFileItemResult]
}

pub enum ProverFileItemResult {
  ProverItemProved(ProverSuccess)
  ProverItemFailed(ProverFailure)
  ProverItemUnfinished(ProverUnfinished)
}
```

```moonbit
test "run scripts" {
  let st = @kernel.empty_kernel_state()
  let opts = @prover.default_prover_options()
  let ok = @prover.prove_theorem_script_detailed(st, "theorem truth_file : ⊢ T := by exact truth", opts)
  inspect(ok is @prover.Proved({ theorem_name: "truth_file", .. }), content="true")
  // the manual's bad_branch example: a structured failure
  let bad = @prover.prove_theorem_script_detailed(
    st,
    "theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by\n  intro h\n  left { exact truth }",
    opts,
  )
  guard bad is @prover.Failed(f) else { fail("expected a failure") }
  inspect(f.detail, content="GoalShapeMismatch(exact witness does not directly close current goal)")
  assert_eq((f.step_index, f.branch_path, f.step_src), (Some(3), [1], Some("exact truth")))
  // a hole is reported, not proved
  let unf = @prover.prove_theorem_script_detailed(
    st,
    "theorem unfinished_branch (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by\n  intro h\n  right { right { hole h1 } }",
    opts,
  )
  guard unf is @prover.Unfinished(u) else { fail("expected an unfinished proof") }
  assert_eq((u.hole_name, u.step_index, u.branch_path), (Some("h1"), Some(4), [1, 1]))
}
```

```moonbit
test "run a file" {
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
  let st = @kernel.empty_kernel_state()
  guard @prover.prove_theorem_file_results_detailed(st, src, @prover.default_prover_options())
    is @prover.FileChecked(report) else {
    fail("expected the file to parse")
  }
  let kinds = report.items.map(item => match item {
    @prover.ProverItemProved(_) => "ok"
    @prover.ProverItemFailed(_) => "error"
    @prover.ProverItemUnfinished(_) => "unfinished"
  })
  assert_eq(kinds, ["ok", "unfinished", "ok"])
}
```

The file is `examples/multi_with_hole.qed`.

## Regression corpus

The corpus is the single list of scripts that the tests run and that the documentation may quote. Each case has an identifier, a script, the layout of its steps, and the capability or failure it demonstrates.

### `positive_corpus_cases`, `negative_corpus_cases`, `unfinished_corpus_cases` and `quantifier_corpus_cases`

These functions return the cases of each kind.

```mbti
pub fn positive_corpus_cases() -> Array[PositiveCorpusCase]
pub fn negative_corpus_cases() -> Array[NegativeCorpusCase]
pub fn unfinished_corpus_cases() -> Array[UnfinishedCorpusCase]
pub fn quantifier_corpus_cases() -> Array[QuantifierCorpusCase]
```

### `PositiveCorpusCase`

A positive case must prove `expected_goal` after declaring the boolean constants `const_names`.

```mbti
pub struct PositiveCorpusCase {
  case_id : String
  const_names : Array[String]
  expected_goal : String
  script : String
  layout : ScriptLayout
  catalog_class : PositiveCatalogClass
  capability : PositiveTacticCapability
}
```

### `NegativeCorpusCase`

A negative case must fail with the error shape `expected_error`. The constants are declared as booleans, unary or binary boolean functions.

```mbti
pub struct NegativeCorpusCase {
  case_id : String
  bool_consts : Array[String]
  unary_bool_consts : Array[String]
  binary_bool_consts : Array[String]
  script : String
  layout : ScriptLayout
  failure_class : NegativeFailureClass
  expected_error : NegativeErrorShape
}
```

### `UnfinishedCorpusCase`

An unfinished case must stop at the given step, branch path and hole, with the given detail.

```mbti
pub struct UnfinishedCorpusCase {
  case_id : String
  const_names : Array[String]
  expected_goal : String
  script : String
  layout : ScriptLayout
  expected_step_index : Int
  expected_branch_path : Array[Int]
  expected_hole_name : String?
  expected_detail : String
}
```

### `QuantifierCorpusCase` and `QuantifierSurfaceOutcome`

A quantifier case covers the binder and raw `forall` surface and may succeed, fail or be unfinished.

```mbti
pub struct QuantifierCorpusCase {
  case_id : String
  script : String
  layout : ScriptLayout
  kind : MappingCaseKind
  outcome : QuantifierSurfaceOutcome
  capability_label : String
  manual_anchor : String
  expected_step_index : Int?
  expected_branch_path : Array[Int]
  expected_hole_name : String?
  expected_detail : String?
}

pub enum QuantifierSurfaceOutcome {
  QuantifierSuccess
  QuantifierFailure
  QuantifierUnfinished
}
```

### `ScriptLayout`, `PositiveCatalogClass`, `PositiveTacticCapability`, `NegativeFailureClass` and `NegativeErrorShape`

These enums classify cases; the label functions below render them as the stable strings used in tests and documentation.

```mbti
pub enum ScriptLayout {
  InlineSequential
  BlockSequential
  BranchStructured
}

pub enum PositiveCatalogClass {
  LocalFact
  DirectClose
  ImplicationBacked
  ContextDerived
  StructuralOnly
}

pub enum PositiveTacticCapability {
  IntroExact
  Assumption
  ExactNamedDirectClose
  ExactContextDerived
  ApplyLocalImp
  ApplyNamedImp
  Split
  Left
  Right
  Mixed
}

pub enum NegativeFailureClass {
  FailureUnknownName
  FailureWrongModeTheoremUsage
  FailureGoalShapeMismatch
  FailureNonBoolConnector
  FailureUnsupportedHonestFailure
  FailureShadowingOrScopeDrift
}

pub enum NegativeErrorShape {
  ErrorTacticUnknownName
  ErrorTacticApplyMismatch
  ErrorTacticGoalShapeMismatch
  ErrorTacticUnsolvedGoals
  ErrorLogicNotBoolTerm
}
```

### `script_layout_label`, `catalog_label`, `capability_label`, `negative_failure_class_label`, `negative_error_shape_label` and `quantifier_surface_outcome_label`

These functions return the stable snake-case label of a classification value, such as `inline_sequential`, `local_fact` or `intro_exact`.

```mbti
pub fn script_layout_label(ScriptLayout) -> String
pub fn catalog_label(PositiveCatalogClass) -> String
pub fn capability_label(PositiveTacticCapability) -> String
pub fn negative_failure_class_label(NegativeFailureClass) -> String
pub fn negative_error_shape_label(NegativeErrorShape) -> String
pub fn quantifier_surface_outcome_label(QuantifierSurfaceOutcome) -> String
```

## Mapping matrix

The mapping matrix links each corpus case to the documentation anchor where it may appear, such as `manual:runnable_examples`, and says whether it is a public example.

### `MappingMatrixEntry` and `mapping_matrix_entries`

```mbti
pub struct MappingMatrixEntry {
  case_id : String
  kind : MappingCaseKind
  script : String
  catalog_or_failure_label : String
  capability_or_error_label : String
  doc_anchor : String
  doc_visibility : MappingDocVisibility
}

pub fn mapping_matrix_entries() -> Array[MappingMatrixEntry]
```

### `MappingCaseKind`, `mapping_case_positive`, `mapping_case_negative` and `mapping_case_unfinished`

`MappingCaseKind` says whether a case is positive, negative or unfinished; the three functions return its constructors.

```mbti
pub enum MappingCaseKind {
  PositiveCase
  NegativeCase
  UnfinishedCase
}

pub fn mapping_case_positive() -> MappingCaseKind
pub fn mapping_case_negative() -> MappingCaseKind
pub fn mapping_case_unfinished() -> MappingCaseKind
```

### `MappingDocVisibility` and its constructor functions

`MappingDocVisibility` says whether a case may be quoted in the documentation as an example, as a failure example, or not at all. `mapping_doc_visibility_public_unfinished_example` returns `PublicExample`: unfinished examples are public examples.

```mbti
pub enum MappingDocVisibility {
  PublicExample
  PublicFailureExample
  InternalOnly
}

pub fn mapping_doc_visibility_public_example() -> MappingDocVisibility
pub fn mapping_doc_visibility_public_failure_example() -> MappingDocVisibility
pub fn mapping_doc_visibility_public_unfinished_example() -> MappingDocVisibility
pub fn mapping_doc_visibility_internal_only() -> MappingDocVisibility
```

```moonbit
test "corpus" {
  let first = @prover.positive_corpus_cases()[0]
  inspect(first.case_id, content="pos_intro_exact_identity")
  inspect(first.script, content="theorem pos_intro_exact_identity : ⊢ P -> P := by intro h; exact h")
  inspect(@prover.capability_label(first.capability), content="intro_exact")
  // every corpus case appears in the mapping matrix with an anchor
  let entry = @prover.mapping_matrix_entries().search_by(e => e.case_id == first.case_id).unwrap()
  inspect(@prover.mapping_matrix_entries()[entry].doc_anchor, content="manual:runnable_examples")
}
```
