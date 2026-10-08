# parser tutorial

This tutorial reads formulas, goals and theorem scripts from text with the `parser` package. You will parse without a kernel state to inspect structure, lower text to kernel terms, locate errors in the original input, and read the step structure of a proof script. The theorem scripts used here come from the regression corpus.

## Quick start

Import the packages in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/logic",
  "Luna-Flow/QED/parser",
}
```

Parse a goal and lower it to kernel terms:

```moonbit
test "quick start" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let goal = @parser.parse_goal(st, "⊢ T").unwrap()
  inspect(@kernel.term_to_string(@parser.parsed_goal_concl(goal)), content="Const(T#1 : bool)")
  inspect(@parser.parsed_goal_hyps(goal).length(), content="0")
}
```

`T` is a constant of the propositional prelude, so the state needs `install_prop_prelude` first.

## Everyday tasks

### Check how a formula groups

`parse_term_raw` needs no state and shows the tree the precedence rules produce:

```moonbit
test "grouping" {
  // ∧ binds tighter than ∨, which binds tighter than ->
  let t = @parser.parse_term_raw("a ∧ b ∨ c -> d").unwrap()
  inspect(t is @parser.Infix("->", @parser.Infix("∨", @parser.Infix("∧", _, _), _), _), content="true")
  // -> associates to the right
  let r = @parser.parse_term_raw("a -> b -> c").unwrap()
  inspect(r is @parser.Infix("->", @parser.Name("a"), @parser.Infix("->", _, _)), content="true")
  // application is juxtaposition and binds tightest
  let app = @parser.parse_term_raw("f x ∧ y").unwrap()
  inspect(app is @parser.Infix("∧", @parser.App(_, _), @parser.Name("y")), content="true")
}
```

### Use ASCII input

You can type `\and`, `\or`, `\not`, `\imp` and `|-`; they are normalised to `∧`, `∨`, `¬`, `->` and `⊢` before parsing:

```moonbit
test "ascii" {
  let a = @parser.parse_goal_raw("p \\and q |- \\not r").unwrap()
  let b = @parser.parse_goal_raw("p ∧ q ⊢ ¬r").unwrap()
  inspect(a.concl is @parser.Prefix("¬", _) && b.concl is @parser.Prefix("¬", _), content="true")
  inspect(@parser.normalize_parser_input("p \\imp q").unwrap().text, content="p -> q")
}
```

### Declare locals and lower terms

Free names must be locals or declared constants. Declare locals with `parse_let` or `parse_env_push_local`:

```moonbit
test "locals" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let env = @parser.parse_let(@parser.empty_parse_env(), "let p : bool").unwrap()
  let env = @parser.parse_let(env, "let q : bool").unwrap()
  let t = @parser.parse_term_with_env(st, env, "p ∧ q -> p").unwrap()
  let (lhs, rhs) = @logic.prop_dest_imp(st, pre, t).unwrap()
  inspect(@logic.prop_dest_and(st, pre, lhs) is Some(_), content="true")
  inspect(@kernel.term_to_string(rhs), content="Var(p : bool)")
  // without the declaration, `r` is unknown
  inspect(@parser.parse_term_with_env(st, env, "p ∧ r") is Err(@parser.Sig(@kernel.UnknownConst)), content="true")
}
```

### Find the position of an error

Error offsets point into the text you passed, even when normalisation changed its length:

```moonbit
test "error position" {
  let src = "p \\and"
  match @parser.parse_term_raw(src) {
    Err(e) => {
      inspect(e.code is @parser.UnexpectedEof, content="true")
      inspect(e.offset, content="6")
      inspect(e.detail, content="unexpected end while parsing atom")
    }
    Ok(_) => fail("expected a parse error")
  }
}
```

The input is six characters long and ends after `\and`, so offset 6 is the end of what the user typed, not of the normalised `p ∧`.

### Read a theorem script

A theorem script parses into a header, a goal and a list of steps with their positions. This is the `demo_and` script from `examples/demo_and.qed`:

```moonbit
test "script structure" {
  let src = "theorem demo_and (x : bool) : ⊢ x -> x ∧ x := by\n  intro h\n  split { exact h } { exact h }"
  let s = @parser.parse_theorem_script_raw(src).unwrap()
  inspect(s.name, content="demo_and")
  inspect(s.binders[0].src, content="(x : bool)")
  let steps = s.body.steps
  inspect(steps[0].step is @parser.Intro("h"), content="true")
  inspect(steps[1].src, content="split") // the step itself; its blocks are branches
  // the two branch blocks of split, each with one step
  let second = steps[1].branches[1]
  inspect(second.body.steps[0].step_index, content="4")
  assert_eq(second.body.steps[0].branch_path, [2])
}
```

Step indices count every step in reading order, including those inside branches: `intro` is 1, `split` is 2, the first `exact` is 3 and the second is 4. The prover reports failures with these numbers.

## Going further

**Lower a quantified goal.** `forall` is accepted at the start of a goal and lowered as a theorem-header binder: the bound name becomes a free variable of the goal.

```moonbit
test "forall goal" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let g = @parser.parse_goal(st, "⊢ forall (x : bool), x -> x").unwrap()
  let free = @kernel.free_vars(@parser.parsed_goal_concl(g))
  inspect(free.length() == 1 && free[0].0 == "x", content="true")
}
```

**Keep identities.** `parse_resolved_term` and `parse_resolved_goal_with_env` return `elab` terms with constant identities frozen; use them when terms are stored and checked later, as the [elab tutorial](elab.md) explains.

**Define functions from text.** `parse_def_function(state, env, "def id(x : bool) : bool { x }")` admits a definition through the kernel and returns its theorem; see the [parser API](../api/parser.md).

**Run the script.** Parsing a script does not prove it. Pass the source text to the [prover](prover.md), which lowers the goal, runs each step with the [tactics](tactics.md) package and reports failures with the spans you saw above.

## Common pitfalls

- **Old connective spellings.** `/\` and `\/` are not accepted; use `∧`, `∨` or `\and`, `\or`.
- **Chained equality.** `a = b = c` is a `NonAssocChain` error; add parentheses.
- **Quantifiers in terms.** `forall` is only allowed at the start of a goal. `parse_term` rejects it with a `Parse` error.
- **Missing turnstile.** A goal needs `⊢` or `|-`, even with no hypotheses: write `⊢ T`, not `T`.
- **`T` and `F` without the prelude.** They are constants, not keywords; without `install_prop_prelude` they are unknown names.
- **Connectives on non-propositions.** `f ∧ p` with `f : bool -> bool` fails at lowering with `Logic(NotBoolTerm)`.

## Next steps

- The [parser API](../api/parser.md) lists every function and syntax type.
- The [parser design](../design/parser.md) explains the grammar and the layering.
- The [syntax guide](../syntax.md) is the user-level reference for theorem scripts.
- The [prover tutorial](prover.md) runs the scripts parsed here.
