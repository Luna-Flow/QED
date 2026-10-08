# elab tutorial

This tutorial resolves names into kernel terms with the `elab` package and shows what happens when the signature changes after resolution. Use it when you build your own frontend on top of the kernel, or when you want to understand the error `ScopeResolutionMismatch` that the parser can report.

| I want to | Use |
| --- | --- |
| Resolve a name to a variable or a constant | `elab_resolve_name`, `elab_resolve_const` |
| Build resolved terms bottom up | `elab_resolve_app`, `elab_resolve_abs`, `elab_resolve_eq` |
| Use a polymorphic constant at an instance | `elab_resolve_const` with the instance type |
| Type-check a resolved term against a state | `elab_check_core_type`, `rterm_well_formed` |
| Turn a resolved term into a kernel term | `elab_lower_to_term` |
| Detect that a term no longer means what it did | `elab_roundtrip_term` |

## Quick start

Import the kernel and `elab` in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/elab",
}
```

Resolve the equation $x = c$, where `x` is a local and `c` a declared constant, and lower it to a kernel term:

```moonbit
test "quick start" {
  let a = @kernel.mk_tyvar("A")
  let st = @kernel.ks_add_const(@kernel.empty_kernel_state(), "c", a).unwrap()
  let ctx = @elab.elab_ctx_from_locals([("x", a)])
  let x = @elab.elab_resolve_name(st, ctx, "x").unwrap()
  let c = @elab.elab_resolve_name(st, ctx, "c").unwrap()
  let eq = @elab.elab_resolve_eq(st, ctx, x, c).unwrap()
  let t = @elab.elab_lower_to_term(eq).unwrap()
  inspect(
    @kernel.term_to_string(t),
    content="Comb(Comb(Const(= : fun(A, fun(A, bool))), Var(x : A)), Const(c#1 : A))",
  )
}
```

The constant comes out as `c#1`: its identity is fixed at resolution time.

## Everyday tasks

### Build terms bottom up

`elab_resolve_app` and `elab_resolve_abs` check types as you build:

```moonbit
test "bottom up" {
  let bool = @kernel.bool_ty()
  let st = @kernel.ks_add_const(@kernel.empty_kernel_state(), "neg", @kernel.fun_ty(bool, bool)).unwrap()
  let ctx = @elab.empty_elab_ctx()
  let neg = @elab.elab_resolve_name(st, ctx, "neg").unwrap()
  // λp. neg p  — the body is checked with p in scope
  let inner = @elab.elab_ctx_extend(ctx, "p", bool)
  let body = @elab.elab_resolve_app(st, inner, neg, @elab.elab_resolve_name(st, inner, "p").unwrap()).unwrap()
  let lam = @elab.elab_resolve_abs(st, ctx, "p", bool, body).unwrap()
  inspect(@elab.elab_check_core_type(st, ctx, lam, @kernel.fun_ty(bool, bool)), content="true")
  // neg applied to itself is rejected
  inspect(@elab.elab_resolve_app(st, ctx, neg, neg) is Err(@elab.CoreTypingFailure), content="true")
}
```

### Use a polymorphic constant at an instance

A constant declared with a type variable can be resolved at any instance of its schema:

```moonbit
test "instances" {
  let a = @kernel.mk_tyvar("A")
  let st = @kernel.ks_add_const(@kernel.empty_kernel_state(), "default", a).unwrap()
  let rc = @elab.elab_resolve_const(st, "default", @kernel.bool_ty()).unwrap()
  inspect(@kernel.hol_type_to_string(@elab.rconst_inst_ty(rc)), content="bool")
  inspect(@kernel.hol_type_to_string(@elab.rconst_schema_ty(rc)), content="A")
  // fun(A, A) is not an instance of the schema bool -> bool of `flip`
  let bool = @kernel.bool_ty()
  let st2 = @kernel.ks_add_const(st, "flip", @kernel.fun_ty(bool, bool)).unwrap()
  let bad = @elab.elab_resolve_const(st2, "flip", @kernel.fun_ty(a, a))
  inspect(bad is Err(@elab.InvalidConstInstance("flip")), content="true")
}
```

### Detect scope drift

A resolved term remembers which declaration each constant meant. After a shadowing declaration, checking it again fails instead of switching to the new constant:

```moonbit
test "scope drift" {
  let bool = @kernel.bool_ty()
  let st1 = @kernel.ks_add_const(@kernel.empty_kernel_state(), "flag", bool).unwrap()
  let ctx = @elab.empty_elab_ctx()
  let flag = @elab.elab_resolve_name(st1, ctx, "flag").unwrap()
  let st2 = @kernel.ks_add_const(@kernel.ks_push_scope(st1), "flag", bool).unwrap()
  inspect(@elab.rterm_well_formed(st2, ctx, flag), content="false")
  // resolving the name again in st2 gives the new constant
  let flag2 = @elab.elab_resolve_name(st2, ctx, "flag").unwrap()
  inspect(@elab.rterm_to_string(flag2), content="RConst(flag#2 : bool <= bool)")
  // back in the outer scope the old term is fine again
  let st3 = @kernel.ks_pop_scope(st2).unwrap()
  inspect(@elab.rterm_well_formed(st3, ctx, flag), content="true")
}
```

## Going further

**Check terms from elsewhere.** `elab_roundtrip_term(state, ctx, t)` re-resolves a kernel term and checks that nothing changed; use it at the boundary where terms built in another state enter your code.

**Inspect a term.** `rterm_collect_consts` lists every constant occurrence with its identity, and `rterm_collect_free_vars` every free variable; both are useful for diagnostics.

**Feed the kernel.** Lower with `elab_lower_to_term` and pass the result to kernel rules. The identities you resolved go with it, and the kernel's admissibility check enforces them again.

**Use the parser instead.** For text input, `@parser.parse_term` and `@parser.parse_resolved_term` run this package for you; see the [parser tutorial](parser.md).

## Common pitfalls

- **Expecting inference.** Binder types are never inferred; pass them to `elab_resolve_abs` or declare locals in the context with their types.
- **Comparing with `rterm_eq`.** It compares bound names too, so α-equivalent terms can differ. Lower both and use `@kernel.term_alpha_eq`.
- **Reusing a context after extension.** `elab_ctx_extend` returns a new context; the old one is unchanged, which is what you want when leaving a binder.
- **Looking for `=` in the state.** Equality is built in and resolves without a declaration; you cannot declare or shadow it.

## Next steps

- The [elab API](../api/elab.md) lists every function and error.
- The [elab design](../design/elab.md) states the freeze property and why it holds.
- The [parser tutorial](parser.md) shows the text frontend built on this package.
