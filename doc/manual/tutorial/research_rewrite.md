# research_rewrite tutorial

This tutorial runs the rewriting prototype of the `research_rewrite` package: rewrite one subterm with a local equation, check the recorded replay obligation, and simplify a connective application. The package is research-only and not part of the shipped prover, so use it to experiment, not to build on.

| I want to | Use |
| --- | --- |
| Rewrite a subterm of a goal with a local equation | `research_rewrite_request`, `research_local_equality`, `research_rewrite_term_concl` |
| Rewrite with a theorem, or right to left | `research_explicit_theorem`, `research_right_to_left` |
| Choose where to rewrite | `research_site_comb_fun`, `research_site_comb_arg` |
| Unfold connectives and β-normalise until nothing changes | `research_simplify_config`, `research_simplify_term_concl` |
| Check a recorded rewrite again | `research_validate_replay_obligation` |

## Quick start

Import the packages in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/logic",
  "Luna-Flow/QED/research_rewrite",
}
```

Rewrite `f p` to `f q` using the local hypothesis `h : p = q`:

```moonbit
test "quick start" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let f = @kernel.mk_var("f", @kernel.fun_ty(bool, bool))
  let locals = [("h", @kernel.mk_eq(p, q).unwrap())]
  let req = @research_rewrite.research_rewrite_request(
    @research_rewrite.research_local_equality("h"),
    @research_rewrite.research_left_to_right(),
    [@research_rewrite.research_site_comb_arg()], // the argument of f p
  )
  match @research_rewrite.research_rewrite_term_concl(st, pre, locals, @kernel.mk_comb(f, p), req) {
    Rewritten(after, _) => inspect(@kernel.term_to_string(after), content="Comb(Var(f : fun(bool, bool)), Var(q : bool))")
    _ => fail("expected a rewrite")
  }
}
```

A request names the equation (a local by name), the direction, and the path to the subterm to replace.

## Everyday tasks

### Check the replay obligation

Each rewrite comes with a record of the kernel steps behind it. Validation rebuilds those steps; it fails when the context they relied on is missing:

```moonbit
test "obligation" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let f = @kernel.mk_var("f", @kernel.fun_ty(bool, bool))
  let locals = [("h", @kernel.mk_eq(p, q).unwrap())]
  let req = @research_rewrite.research_rewrite_request(
    @research_rewrite.research_local_equality("h"),
    @research_rewrite.research_left_to_right(),
    [@research_rewrite.research_site_comb_arg()],
  )
  guard @research_rewrite.research_rewrite_term_concl(st, pre, locals, @kernel.mk_comb(f, p), req)
    is Rewritten(_, obligation) else {
    fail("expected a rewrite")
  }
  inspect(@research_rewrite.research_validate_replay_obligation(st, pre, locals, obligation) is Ok(_), content="true")
  inspect(@research_rewrite.research_validate_replay_obligation(st, pre, [], obligation) is Err(_), content="true")
}
```

### Simplify a connective

`research_simplify_term_concl` unfolds connective constants and β-normalises until nothing changes:

```moonbit
test "simplify" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let not_p = @kernel.mk_comb(@kernel.ks_mk_const(st, "not").unwrap(), p) // the constant `not` applied to p
  let cfg = @research_rewrite.research_simplify_config(10, true, true, [])
  match @research_rewrite.research_simplify_term_concl(st, pre, [], not_p, cfg) {
    Rewritten(after, obligation) => {
      inspect(@kernel.term_alpha_eq(after, @logic.prop_mk_not(st, pre, p).unwrap()), content="true")
      inspect(obligation.segments.length(), content="1")
    }
    _ => fail("expected a simplification")
  }
  // a variable has nothing to simplify
  inspect(@research_rewrite.research_simplify_term_concl(st, pre, [], p, cfg) is NoChange, content="true")
}
```

### See the honest failures

Unsupported requests say why they fail:

```moonbit
test "failures" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let not_p = @kernel.mk_comb(@kernel.ks_mk_const(st, "not").unwrap(), p)
  // a step limit of 0 allows no segment
  let tight = @research_rewrite.research_simplify_config(0, true, true, [])
  match @research_rewrite.research_simplify_term_concl(st, pre, [], not_p, tight) {
    HonestFailure(msg) => inspect(msg, content="step limit exceeded")
    _ => fail("expected a failure")
  }
  // the path asks for an abstraction where there is an application
  let req = @research_rewrite.research_rewrite_request(
    @research_rewrite.research_beta_normalization(),
    @research_rewrite.research_left_to_right(),
    [@research_rewrite.research_site_abs_body()],
  )
  match @research_rewrite.research_rewrite_term_concl(st, pre, [], not_p, req) {
    HonestFailure(msg) => inspect(msg, content="rewrite site expected a lambda abstraction")
    _ => fail("expected a failure")
  }
}
```

## Going further

**Rewrite with a theorem.** `research_explicit_theorem(th)` uses any equation theorem as the witness, for example one from `@logic.logic_eq_sym`. Combine it with `research_right_to_left()` to rewrite in the other direction.

**Chain requests.** Put several requests into `SimplifyConfig.rewrite_requests`; each round applies those that match, and the obligation records one segment per applied step.

**Read the research notes.** The design and the promotion gates are in `research/rewrite-simplify/`; the [research_rewrite design](../design/research_rewrite.md) summarises what is missing for promotion.

## Common pitfalls

- **Expecting a theorem.** A rewrite returns a term and an obligation. Nothing proves the original goal.
- **Rewriting under λ.** `AbsBody` sites are rejected.
- **Folding definitions.** `CanonicalUnfold` and `BetaNormalization` only work left to right.
- **Depending on the package.** It is research-only and may change or be removed.

## Next steps

- The [research_rewrite API](../api/research_rewrite.md) lists every type and function.
- The [research_rewrite design](../design/research_rewrite.md) explains conversions and replay obligations.
- The [tactics tutorial](tactics.md) shows the shipped way to prove goals.
