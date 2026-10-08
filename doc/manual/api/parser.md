# parser API

The `parser` package (`Luna-Flow/QED/parser`) is the text frontend. It normalises input, parses terms, goals and theorem scripts into syntax trees that keep positions in the original text, and lowers terms and goals to kernel terms through the `elab` and `logic` packages. It owns no tactic objects: a parsed goal is a parser-owned `ParsedGoal`, which the `prover` bridges to the tactics layer.

Functions ending in `_raw` only parse. The others also resolve names and build kernel terms against a `KernelState`. The surface syntax is summarised in the [syntax guide](../syntax.md); the choices behind it are in the [parser design](../design/parser.md), and the [parser tutorial](../tutorial/parser.md) parses and lowers step by step.

## Input normalisation

### `NormalizedInput`

`NormalizedInput` is the normalised text together with a map back to the raw input.

```mbti
pub struct NormalizedInput {
  text : String
  raw_offsets : Array[Int]
  raw_length : Int
}
```

`raw_offsets[i]` is the offset in the raw input of character `i` of `text`, and `raw_length` is the length of the raw input.

### `normalize_parser_input`

`normalize_parser_input` rewrites the compatibility spellings to the canonical ones and collapses runs of whitespace.

```mbti
pub fn normalize_parser_input(String) -> Result[NormalizedInput, ParseError]
```

`\not`, `\and`, `\or` and `\imp` become `¬`, `∧`, `∨` and `->`, and `|-` becomes `⊢`. The old spellings `/\` and `\/` are not accepted. Every parsing function calls this first.

### `normalized_input_raw_offset_at`

`normalized_input_raw_offset_at(input, i)` maps an offset in the normalised text back to the raw input.

```mbti
pub fn normalized_input_raw_offset_at(NormalizedInput, Int) -> Int
```

Offsets in `ParseError` and in source spans are already mapped back, so error positions always refer to what the user typed.

### `SourceSpan` and `source_span`

`SourceSpan` is a half-open range of raw offsets. `source_span(start, end)` builds one, clamping a negative start to 0 and an end before the start to the start.

```mbti
pub struct SourceSpan {
  start_offset : Int
  end_offset : Int
}

pub fn source_span(Int, Int) -> SourceSpan
```

```moonbit
test "normalise" {
  let n = @parser.normalize_parser_input("p  \\and  q |- r").unwrap()
  inspect(n.text, content="p ∧ q ⊢ r")
  // `∧` (offset 2 in the normalised text) came from `\and` at offset 3
  inspect(@parser.normalized_input_raw_offset_at(n, 2), content="3")
  let sp = @parser.source_span(5, 2)
  assert_eq((sp.start_offset, sp.end_offset), (5, 5))
}
```

## Errors

### `ParseError` and `ParseErrorCode`

`ParseError` is a syntax error at a raw offset, with a human-readable detail.

```mbti
pub struct ParseError {
  code : ParseErrorCode
  offset : Int
  detail : String
}

pub enum ParseErrorCode {
  UnexpectedToken
  UnexpectedEof
  MissingTurnstile
  NonAssocChain
  UnknownOperator
  EmptyConclusion
  EmptyHypothesis
}
```

| Code | Meaning |
| --- | --- |
| `UnexpectedToken` | A token that cannot appear here, including raw `forall` in a term and an unknown step keyword. |
| `UnexpectedEof` | The input ended in the middle of a construct. |
| `MissingTurnstile` | A goal has no `⊢`. |
| `NonAssocChain` | A chain such as `a = b = c` of the non-associative operator `=`. |
| `UnknownOperator` | An operator outside the fixity table. |
| `EmptyConclusion` | A goal has nothing after `⊢`. |
| `EmptyHypothesis` | A goal has an empty hypothesis between commas. |

### `ParseBridgeError`

`ParseBridgeError` is the error of the functions that parse and lower: a syntax error, or an error from the kernel or the resolver.

```mbti
pub enum ParseBridgeError {
  Parse(ParseError)
  Sig(@kernel.SigError)
  Logic(@kernel.LogicError)
  Elab(@elab.ElabError)
}
```

A name that is neither a local nor a declared constant reports `Sig(UnknownConst)`; a connective applied to a non-proposition reports `Logic(NotBoolTerm)`.

## Local environments

### `ParseEnv`

`ParseEnv` is the list of local variables visible to the parser, innermost last.

```mbti
pub struct ParseEnv {
  locals : Array[(String, @kernel.HolType)]
}
```

Names are resolved locals first, then constants.

### `empty_parse_env`, `parse_env_push_local`, `parse_env_local_count` and `parse_env_local_at`

These functions build and read environments; `parse_env_push_local` returns a new environment.

```mbti
pub fn empty_parse_env() -> ParseEnv
pub fn parse_env_push_local(ParseEnv, String, @kernel.HolType) -> ParseEnv
pub fn parse_env_local_count(ParseEnv) -> Int
pub fn parse_env_local_at(ParseEnv, Int) -> (String, @kernel.HolType)?
```

### `parse_let`

`parse_let(env, src)` parses a declaration `let <name> : <type>` and returns the environment with that local added.

```mbti
pub fn parse_let(ParseEnv, String) -> Result[ParseEnv, ParseBridgeError]
```

Types are type names (`bool`, `ind`, or a type variable such as `A`) and arrows between them: `let f : A -> bool`.

## Terms

### `SynTerm`

`SynTerm` is the syntax tree of a term.

```mbti
pub enum SynTerm {
  Name(String)
  Prefix(String, SynTerm)
  App(SynTerm, SynTerm)
  Infix(String, SynTerm, SynTerm)
  Forall(String, @kernel.HolType, SynTerm)
}
```

`Prefix` is `¬`; `Infix` is one of `=`, `∧`, `∨`, `->`; `App` is juxtaposition. `Forall` only arises from goal syntax.

### `parse_term_raw`

`parse_term_raw` parses a term without resolving names.

```mbti
pub fn parse_term_raw(String) -> Result[SynTerm, ParseError]
```

Application binds tightest, then `¬`, then the infix operators by this table:

| Operator | Precedence | Associativity |
| --- | --- | --- |
| `=` | 40 | none |
| `∧` | 30 | left |
| `∨` | 20 | left |
| `->` | 15 | right |

So `p ∧ q ∨ ¬p -> q` reads $((p \wedge q) \vee \neg p) \Rightarrow q$, and `a = b = c` is an error.

### `parse_term`, `parse_term_with_env` and `lower_syn_term_with_env`

These functions produce a kernel term. `parse_term(state, src)` parses with no locals; `parse_term_with_env` uses an environment; `lower_syn_term_with_env` lowers an already parsed `SynTerm`.

```mbti
pub fn parse_term(@kernel.KernelState, String) -> Result[@kernel.Term, ParseBridgeError]
pub fn parse_term_with_env(@kernel.KernelState, ParseEnv, String) -> Result[@kernel.Term, ParseBridgeError]
pub fn lower_syn_term_with_env(@kernel.KernelState, ParseEnv, SynTerm) -> Result[@kernel.Term, ParseBridgeError]
```

Names resolve through `elab`; connectives are built with the `logic` builders, so `p ∧ q` becomes the basis term of `prop_mk_and` and the prelude need not be installed for them. The constants `T` and `F` are ordinary names and need the prelude.

### `parse_resolved_term` and `parse_resolved_term_with_env`

These functions stop one step earlier and return the resolved term, with constant identities frozen.

```mbti
pub fn parse_resolved_term(@kernel.KernelState, String) -> Result[@elab.RTerm, ParseBridgeError]
pub fn parse_resolved_term_with_env(@kernel.KernelState, ParseEnv, String) -> Result[@elab.RTerm, ParseBridgeError]
```

```moonbit
test "terms" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let env = @parser.parse_let(@parser.empty_parse_env(), "let p : bool").unwrap()
  let env = @parser.parse_let(env, "let q : bool").unwrap()
  let syn = @parser.parse_term_raw("p ∧ q ∨ ¬p -> q").unwrap()
  inspect(syn is @parser.Infix("->", @parser.Infix("∨", _, _), _), content="true")
  let t = @parser.parse_term_with_env(st, env, "p ∧ q").unwrap()
  inspect(@logic.prop_dest_and(st, pre, t) is Some(_), content="true")
  inspect(@kernel.term_to_string(@parser.parse_term(st, "T").unwrap()), content="Const(T#1 : bool)")
  // errors
  inspect(@parser.parse_term(st, "x") is Err(@parser.Sig(@kernel.UnknownConst)), content="true")
  inspect(@parser.parse_term_raw("p = q = p") is Err({ code: @parser.NonAssocChain, .. }), content="true")
  let env_f = @parser.parse_let(env, "let f : bool -> bool").unwrap()
  inspect(@parser.parse_term_with_env(st, env_f, "f ∧ p") is Err(@parser.Logic(@kernel.NotBoolTerm)), content="true")
}
```

## Goals

### `SynGoal`

`SynGoal` is the syntax tree of a sequent goal `h1, h2 ⊢ c`.

```mbti
pub struct SynGoal {
  hyps : Array[SynTerm]
  concl : SynTerm
}
```

### `parse_goal_raw`

`parse_goal_raw` parses a goal without resolving names. The hypotheses are separated by commas; `⊢` (or `|-`) is required.

```mbti
pub fn parse_goal_raw(String) -> Result[SynGoal, ParseError]
```

A goal, unlike a term, may start with `forall (x : A), body` or `∀ (x : A), body`, also in parentheses. This form is accepted only here, as goal sugar.

### `ParsedGoal`, `parsed_goal_hyps` and `parsed_goal_concl`

`ParsedGoal` is a lowered goal: kernel terms for the hypotheses and the conclusion. The two accessors read them.

```mbti
pub struct ParsedGoal {
  hyps : Array[@kernel.Term]
  concl : @kernel.Term
}

pub fn parsed_goal_hyps(ParsedGoal) -> Array[@kernel.Term]
pub fn parsed_goal_concl(ParsedGoal) -> @kernel.Term
```

The prover turns a `ParsedGoal` into a `@tactics.Goal`; the parser does not depend on the tactics package.

### `parse_goal`, `parse_goal_with_env` and `lower_syn_goal_with_env`

These functions parse and lower a goal, with no locals, with an environment, or from a parsed `SynGoal`.

```mbti
pub fn parse_goal(@kernel.KernelState, String) -> Result[ParsedGoal, ParseBridgeError]
pub fn parse_goal_with_env(@kernel.KernelState, ParseEnv, String) -> Result[ParsedGoal, ParseBridgeError]
pub fn lower_syn_goal_with_env(@kernel.KernelState, ParseEnv, SynGoal) -> Result[ParsedGoal, ParseBridgeError]
```

Every hypothesis and the conclusion must be propositions (`Logic(NotBoolTerm)` otherwise). A `forall (x : A), body` goal is lowered with `x` as a local of type `A`.

### `ResolvedGoal` and `parse_resolved_goal_with_env`

`ResolvedGoal` is a goal of resolved terms; `parse_resolved_goal_with_env` produces one.

```mbti
pub struct ResolvedGoal {
  hyps : Array[@elab.RTerm]
  concl : @elab.RTerm
}

pub fn parse_resolved_goal_with_env(@kernel.KernelState, ParseEnv, String) -> Result[ResolvedGoal, ParseBridgeError]
```

```moonbit
test "goals" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let env = @parser.parse_env_push_local(@parser.empty_parse_env(), "p", @kernel.bool_ty())
  let g = @parser.parse_goal_with_env(st, env, "p, p ⊢ p ∧ p").unwrap()
  inspect(@parser.parsed_goal_hyps(g).length(), content="2")
  // goal-only quantifier sugar
  inspect(@parser.parse_goal(st, "⊢ forall (x : bool), x -> x") is Ok(_), content="true")
  inspect(@parser.parse_term(st, "forall (x : bool), x") is Err(@parser.Parse(_)), content="true")
  inspect(@parser.parse_goal(st, "T") is Err(@parser.Parse({ code: @parser.MissingTurnstile, .. })), content="true")
}
```

## Theorem scripts

### `SynTheoremScript`

`SynTheoremScript` is a parsed theorem script `theorem <name> <binders> : <goal> := by <steps>`.

```mbti
pub struct SynTheoremScript {
  name : String
  binders : Array[SynBinder]
  goal : SynGoal
  goal_src : String
  goal_span : SourceSpan
  body : SynScriptBody
}
```

`goal_src` is the goal text as written and `goal_span` its raw position.

### `SynBinder`

`SynBinder` is a theorem-header binder `(x : bool)` with its position and source text.

```mbti
pub struct SynBinder {
  name : String
  ty : @kernel.HolType
  span : SourceSpan
  src : String
}
```

### `SynScriptBody`, `SynScriptStep` and `SynScriptBranch`

A body is a list of steps. Each step records its index (counting from 1 across the whole script), the branch path it belongs to, its position and source text, and the branch blocks written after it.

```mbti
pub struct SynScriptBody {
  steps : Array[SynScriptStep]
}

pub struct SynScriptStep {
  step : SynTacticStep
  step_index : Int
  branch_path : Array[Int]
  span : SourceSpan
  src : String
  branches : Array[SynScriptBranch]
}

pub struct SynScriptBranch {
  branch_path : Array[Int]
  body : SynScriptBody
  span : SourceSpan
  src : String
}
```

`split { ... } { ... }` has two branches with paths `[1]` and `[2]` relative to the enclosing path; `left { ... }` and `right { ... }` have one. Nested blocks extend the path.

### `SynTacticStep`

`SynTacticStep` is one proof step.

```mbti
pub enum SynTacticStep {
  Intro(String)
  Exact(String)
  Apply(String)
  Assumption
  Split
  Left
  Right
  Hole(String?)
}
```

`Hole` is parser-only: the tactics layer has no hole step, and the prover turns a hole into an unfinished result.

### `parse_theorem_script_raw` and `parse_theorem_file_raw`

`parse_theorem_script_raw` parses one theorem script. Steps may be on one line separated by `;`, or one per line. `parse_theorem_file_raw` parses a file of scripts separated by lines containing `qed`; a file with a single theorem may omit it.

```mbti
pub fn parse_theorem_script_raw(String) -> Result[SynTheoremScript, ParseError]
pub fn parse_theorem_file_raw(String) -> Result[Array[SynTheoremScript], ParseError]
```

Binder types and goals are parsed but not resolved; the prover lowers them.

```moonbit
test "scripts" {
  let s = @parser.parse_theorem_script_raw(
    "theorem dup (x : bool) : ⊢ x -> x ∧ x := by\n  intro h\n  split { exact h } { exact h }",
  ).unwrap()
  assert_eq((s.name, s.binders.length(), s.goal_src), ("dup", 1, "⊢ x -> x ∧ x"))
  let split = s.body.steps[1]
  inspect(split.step is @parser.Split, content="true")
  assert_eq(split.branches.map(b => b.branch_path), [[1], [2]])
  let h = @parser.parse_theorem_script_raw("theorem t : ⊢ T := by hole h1").unwrap()
  inspect(h.body.steps[0].step is @parser.Hole(Some("h1")), content="true")
  let file = @parser.parse_theorem_file_raw(
    "theorem a : ⊢ T := by exact truth\nqed\ntheorem b : ⊢ T := by exact truth\nqed\n",
  ).unwrap()
  inspect(file.length(), content="2")
}
```

## Definitions

### `parse_def_function`

`parse_def_function(state, env, src)` parses a definition `def <name>(<x> : <type>, ...) : <type> { <body> }` and admits it through the kernel's `DefOK` gate as the constant $\mathit{name} = \lambda x \dots.\,\mathit{body}$.

```mbti
pub fn parse_def_function(@kernel.KernelState, ParseEnv, String) -> Result[(@kernel.KernelState, @kernel.Thm), ParseBridgeError]
```

It returns the extended state and the definition theorem. Kernel refusals (a free variable in the body, a name already defined) come back as `Sig` errors. This utility is not part of theorem-script syntax.

```moonbit
test "definition" {
  let st = @kernel.empty_kernel_state()
  let (st2, th) = @parser.parse_def_function(st, @parser.empty_parse_env(), "def id(x : bool) : bool { x }").unwrap()
  inspect(@kernel.ks_has_def_head(st2, "id"), content="true")
  inspect(
    @kernel.term_to_string(@kernel.thm_concl(th).unwrap()),
    content="Comb(Comb(Const(= : fun(fun(bool, bool), fun(fun(bool, bool), bool))), Const(id#1 : fun(bool, bool))), Abs(Var(_b0 : bool), Var(_b0 : bool)))",
  )
  // defining the same name twice is refused by the kernel
  let again = @parser.parse_def_function(st2, @parser.empty_parse_env(), "def id(x : bool) : bool { x }")
  inspect(again is Err(@parser.Sig(@kernel.DefinitionAlreadyExists)), content="true")
}
```
