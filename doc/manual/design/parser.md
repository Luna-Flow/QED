# parser design

The `parser` package turns text into syntax trees and syntax trees into kernel terms. It is untrusted and deliberately narrow: it fixes the surface notation, reports errors at positions the user can find, and hands goals upward as plain data. This page explains the grammar, the lowering path and the boundary to the tactics layer.

## Design goal

- Accept a small, unambiguous notation for propositional goals and proof scripts, with Unicode as the canonical form and ASCII spellings as input conveniences.
- Report every syntax error at an offset in the text the user wrote, even after normalisation.
- Lower to kernel terms only through the resolution boundary of `elab` and the connective builders of `logic`, so the parser never decides what a name or a connective means.
- Stay below the tactics layer: produce goals, never proof states.

## Mathematical background

### Grammar

Terms follow this grammar, where *name* is an identifier and application is juxtaposition:

$$
\begin{aligned}
\mathit{term} &::= \mathit{term}\ \mathit{op}\ \mathit{term} \mid \neg\,\mathit{term} \mid \mathit{app} \\
\mathit{app} &::= \mathit{atom}^{+} \\
\mathit{atom} &::= \mathit{name} \mid (\,\mathit{term}\,) \\
\mathit{op} &::= {=} \mid {\wedge} \mid {\vee} \mid {\to}
\end{aligned}
$$

Negation is a prefix operator that binds tighter than every infix operator, so `¬ a ∧ b` is `(¬ a) ∧ b`. The ambiguity of the first production is resolved by precedence and associativity:

| Operator | Precedence | Associativity | Reading of a chain |
| --- | --- | --- | --- |
| `=` | 40 | none | `a = b = c` is an error |
| `∧` | 30 | left | `a ∧ b ∧ c` is `(a ∧ b) ∧ c` |
| `∨` | 20 | left | `a ∨ b ∨ c` is `(a ∨ b) ∨ c` |
| `->` | 15 | right | `a -> b -> c` is `a -> (b -> c)` |

Goals are sequents $h_1, \dots, h_n \vdash c$, and a goal may start with `forall (x : A), ...`. Theorem scripts add a header with binders and a body of steps, with optional `{ ... }` branch blocks after `split`, `left` and `right`.

### Operator-precedence parsing

An infix chain $t_0\ o_1\ t_1\ \dots\ o_n\ t_n$ is parsed with an operator stack. When a new operator $o$ arrives with an operator $o'$ on top of the stack, the parser reduces $o'$ first exactly when

$$
\mathrm{prec}(o') > \mathrm{prec}(o)
\;\lor\;
\big(\mathrm{prec}(o') = \mathrm{prec}(o) \land \text{both are left-associative}\big),
$$

keeps $o'$ when the precedence is lower or both are right-associative, and fails with `NonAssocChain` when the precedences are equal and one of them is non-associative. Each operator is pushed and popped once, so the algorithm is linear in the length of the chain, and it produces the unique tree that respects the table.

### Lowering

Lowering maps syntax to kernel terms:

$$
\begin{aligned}
[\![x]\!]_\Gamma &= x{:}\tau &&\text{if } (x:\tau) \in \Gamma \\
[\![c]\!]_\Gamma &= c^{\iota}{:}\sigma &&\text{if } c \text{ is declared with identity } \iota \text{ and schema } \sigma \\
[\![a\ b]\!]_\Gamma &= [\![a]\!]_\Gamma\,[\![b]\!]_\Gamma \\
[\![a = b]\!]_\Gamma &= ([\![a]\!]_\Gamma = [\![b]\!]_\Gamma) \\
[\![a \wedge b]\!]_\Gamma &= \texttt{prop\_mk\_and}([\![a]\!]_\Gamma, [\![b]\!]_\Gamma) &&\text{and likewise for } \vee, \to, \neg
\end{aligned}
$$

Names go through `elab` (locals before constants, identities frozen), connectives through the `logic` builders, which check that their arguments are propositions. A goal `forall (x : A), body` is lowered by adding $x{:}A$ to $\Gamma$ and lowering `body`: the quantifier is dropped and $x$ stays free in the goal, exactly as for a theorem-header binder `(x : A)`. A theorem with a free variable holds for every value of it, because INST can substitute any term of the same type, so $\vdash \mathit{body}$ with $x$ free is the HOL reading of the quantified statement.

## Design decisions

### Normalise first, keep an offset map

**Problem.** Users type `\and`, `|-` or extra spaces; error messages must point at what they typed.

**Choice.** `normalize_parser_input` rewrites the input once into canonical text and records, for every character, its raw offset. The lexer and parser work on the canonical text, and every error offset and span is mapped back before it leaves the package.

**Why.** One canonical form keeps the grammar small, and the map keeps diagnostics honest. The old ASCII spellings `/\` and `\/` are no longer accepted, so there is one ASCII spelling per connective.

### Raw parsing separate from lowering

**Problem.** Lowering needs a kernel state; tools such as the prover need the script structure before any state exists, for example to report the position of a step.

**Choice.** Every construct has a `_raw` parser that returns a syntax tree with positions and no state, and a lowering function that takes the state. Theorem scripts are only parsed raw; the prover lowers their goals itself.

**Why.** The prover can blame a failing step by its span and index without re-parsing, and the parser stays independent of proof execution.

### A parser-owned goal

**Problem.** The obvious return type for `parse_goal` is the tactics package's `Goal`, but then the parser would depend on the tactics layer and changes there would ripple into syntax.

**Choice.** The parser returns its own `ParsedGoal`; the prover converts it with `@tactics.mk_goal`.

**Why.** It keeps the layer order `kernel → logic/elab → parser → tactics → prover` acyclic, as [code governance](../code_governance.md) requires, and it means the parser cannot construct proof objects even by mistake.

### Connectives are built, not looked up

Connectives are lowered with the `logic` builders to basis terms; the parser does not require constants named `and` or `imp` to exist. This gives every connective the same meaning in every state, and lets the parser report a non-proposition argument as `Logic(NotBoolTerm)` at lowering time instead of leaving it to a tactic.

### Quantifiers only as goal sugar

Raw `forall` is accepted at the start of a goal and nowhere else. A general binder in terms would need a quantifier constant and its rules in the logic layer, which the shipped subset does not have. Accepting it only at the start of a goal, where it means the same as a theorem-header binder, keeps the surface honest: anything that lowers can be proved by the existing machinery. `forall` inside a term is refused with `UnexpectedToken`. In a term the raw parser already refuses it, at its position. In a goal the raw parser accepts it after an operator, as in `⊢ p -> forall (x : bool), x`, and the error comes from lowering; that error carries offset 0 instead of the position of `forall`.

### Positions on every step

Every script step records its index, its branch path and its span. These are the fields the prover and the CLI report on failure and for unfinished proofs, so a user sees `step: 3`, `branch: 1` and the source text instead of a bare error.

## Correctness and invariants

- **No authority.** The parser builds terms and, through `parse_def_function`, calls the kernel's `DefOK` gate. It produces no theorem by any other route.
- **Offsets refer to raw input.** For every `ParseError` and `SourceSpan`, offsets are positions in the original string, within $[0, \text{raw length}]$. Lowering errors carry no position of their own: `Elab`, `Logic` and `Sig` errors have none, and the few `Parse` errors raised during lowering, such as the nested `forall` above, use offset 0.
- **Deterministic structure.** The precedence table defines one tree for every accepted chain; chains of `=` are rejected rather than guessed.
- **Locals before constants.** A binder or `let` local shadows a constant with the same name, consistently with `elab` and the tactics layer.
- **Step numbering.** `step_index` counts steps from 1 in source order across the whole script, including steps inside branch blocks, so the number in a diagnostic matches the reading order of the script.

## Alternatives rejected

- **A parser generator.** The grammar is small enough that a hand-written lexer and operator-precedence parser is shorter, gives better error offsets, and needs no build step.
- **Returning tactics objects.** Rejected for layering, as above.
- **Full HOL term syntax** with typed binders, type annotations and quantifiers everywhere. It would invite scripts the tactics layer cannot prove; the syntax grows only together with the proof machinery.
- **Implicit `T` and `F`.** They are ordinary constant names resolved through the state, so a script fails visibly when the prelude is missing instead of silently using another meaning.

## Boundaries

- No type inference: binder and `let` types are written explicitly; there are no type annotations inside terms.
- No `forall` or `exists` inside terms, no λ-abstraction syntax, and no user-defined operators.
- No pretty-printer: terms are rendered by the kernel's structural printers.
- No proof execution: steps are parsed into `SynTacticStep` values, run by the [tactics](tactics.md) package and scheduled by the [prover](prover.md).
