# elab API

## Purpose

The `elab` package (`Luna-Flow/QED/elab`) is the resolution boundary between names and the kernel. It resolves each name of a term once, against a local context and a kernel state, into a *resolved term* `RTerm` whose constants carry their kernel identity; it type-checks resolved terms against the state; and it lowers them to kernel terms. It also offers thin builders for kernel terms with type checks. It depends only on `kernel` and produces no theorems.

The design behind the frozen identities is in the [elab design](../design/elab.md); the [elab tutorial](../tutorial/elab.md) walks through resolution and scope changes.

## Importing

Add the package to your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/QED/elab",
  "Luna-Flow/QED/kernel",
}
```

The examples on this page are blackbox tests. They refer to this package as `@elab` and also use `@kernel`, so they import both packages.

## Contexts

### `ElabCtx`

`ElabCtx` is a local context: an ordered list of variable names with their types, innermost last.

```mbti
pub struct ElabCtx {
  locals : Array[(String, @kernel.HolType)]
}
```

### `empty_elab_ctx`, `elab_ctx_from_locals` and `elab_ctx_extend`

These functions build contexts. `elab_ctx_extend` returns a new context with one more local; the argument is not changed.

```mbti
pub fn empty_elab_ctx() -> ElabCtx
pub fn elab_ctx_from_locals(Array[(String, @kernel.HolType)]) -> ElabCtx
pub fn elab_ctx_extend(ElabCtx, String, @kernel.HolType) -> ElabCtx
```

A later local with the same name shadows an earlier one.

## Resolved terms

### `ResolvedConst`

`ResolvedConst` is a constant occurrence frozen at resolution time.

```mbti
pub struct ResolvedConst {
  name : String
  const_id : Int
  inst_ty : @kernel.HolType
  schema_ty : @kernel.HolType
}
```

`const_id` is the kernel identity the name resolved to, `schema_ty` the declared schema at that time, and `inst_ty` the type of this occurrence, an instance of `schema_ty`. The built-in equality has `const_id == -1` and schema $\alpha \to \alpha \to \mathit{bool}$.

### `RTerm`

`RTerm` is a resolved term: a named term in which every constant is a `ResolvedConst`.

```mbti
pub enum RTerm {
  RVar(String, @kernel.HolType)
  RConst(ResolvedConst)
  RComb(RTerm, RTerm)
  RAbs(String, @kernel.HolType, RTerm)
}
```

### `rterm_var`, `rterm_const`, `rterm_comb` and `rterm_abs`

These functions build resolved terms without checking them.

```mbti
pub fn rterm_var(String, @kernel.HolType) -> RTerm
pub fn rterm_const(ResolvedConst) -> RTerm
pub fn rterm_comb(RTerm, RTerm) -> RTerm
pub fn rterm_abs(String, @kernel.HolType, RTerm) -> RTerm
```

### `rconst_name`, `rconst_id`, `rconst_inst_ty` and `rconst_schema_ty`

These functions read the fields of a `ResolvedConst`.

```mbti
pub fn rconst_name(ResolvedConst) -> String
pub fn rconst_id(ResolvedConst) -> Int
pub fn rconst_inst_ty(ResolvedConst) -> @kernel.HolType
pub fn rconst_schema_ty(ResolvedConst) -> @kernel.HolType
```

### `rterm_eq`

`rterm_eq` is structural equality of resolved terms, including bound names and constant identities. It is not α-equivalence.

```mbti
pub fn rterm_eq(RTerm, RTerm) -> Bool
```

### `rterm_collect_free_vars` and `rterm_collect_consts`

`rterm_collect_free_vars` lists the free variables of a resolved term, in order of occurrence and with repetitions. `rterm_collect_consts` lists every constant occurrence.

```mbti
pub fn rterm_collect_free_vars(RTerm) -> Array[(String, @kernel.HolType)]
pub fn rterm_collect_consts(RTerm) -> Array[ResolvedConst]
```

### `rterm_to_string`

`rterm_to_string` renders a resolved term; a constant prints as `RConst(name#id : inst <= schema)`.

```mbti
pub fn rterm_to_string(RTerm) -> String
```

## Resolution

### `elab_resolve_name`

`elab_resolve_name(state, ctx, name)` resolves a name: a local of `ctx` if there is one, otherwise the constant visible in `state` at its schema type. Locals take precedence over constants.

```mbti
pub fn elab_resolve_name(@kernel.KernelState, ElabCtx, String) -> Result[RTerm, ElabError]
```

Fails with `UnknownName(name)` when the name is neither.

### `elab_resolve_const`, `elab_resolve_const_by_name` and `elab_resolve_const_instance`

These functions resolve a constant. `elab_resolve_const(state, name, ty)` resolves an occurrence at the type `ty`; `elab_resolve_const_by_name` uses the schema type; `elab_resolve_const_instance` wraps the result in `RConst`.

```mbti
pub fn elab_resolve_const(@kernel.KernelState, String, @kernel.HolType) -> Result[ResolvedConst, ElabError]
pub fn elab_resolve_const_by_name(@kernel.KernelState, String) -> Result[ResolvedConst, ElabError]
pub fn elab_resolve_const_instance(@kernel.KernelState, String, @kernel.HolType) -> Result[RTerm, ElabError]
```

The name `=` always resolves to the built-in equality. Failures: `UnknownConst(name)` when nothing is declared, `InvalidConstInstance(name)` when the type is not an instance of the schema, and `ScopeResolutionMismatch` when the state's identity and schema tables disagree.

### `elab_resolve_var`

`elab_resolve_var` builds a resolved variable without consulting a context.

```mbti
pub fn elab_resolve_var(String, @kernel.HolType) -> RTerm
```

### `elab_resolve_app`, `elab_resolve_abs` and `elab_resolve_eq`

These functions build an application, an abstraction or an equation from resolved parts and type-check the result against the state and context.

```mbti
pub fn elab_resolve_app(@kernel.KernelState, ElabCtx, RTerm, RTerm) -> Result[RTerm, ElabError]
pub fn elab_resolve_abs(@kernel.KernelState, ElabCtx, String, @kernel.HolType, RTerm) -> Result[RTerm, ElabError]
pub fn elab_resolve_eq(@kernel.KernelState, ElabCtx, RTerm, RTerm) -> Result[RTerm, ElabError]
```

They fail with `CoreTypingFailure` when the result is ill-typed. For `elab_resolve_abs`, the body is checked in `ctx` extended with the binder.

### `elab_resolve_named_term` and `elab_roundtrip_term`

`elab_resolve_named_term(state, ctx, t)` resolves an existing kernel term: free variables must be locals of `ctx` with the same type, and constants are looked up again by name in `state`. `elab_roundtrip_term` also lowers the result and checks that it is α-equivalent to `t`, constant identities included.

```mbti
pub fn elab_resolve_named_term(@kernel.KernelState, ElabCtx, @kernel.Term) -> Result[RTerm, ElabError]
pub fn elab_roundtrip_term(@kernel.KernelState, ElabCtx, @kernel.Term) -> Result[RTerm, ElabError]
```

`elab_roundtrip_term` fails with `ScopeResolutionMismatch` when a constant of `t` now resolves to another identity, which is how a term built in one scope is detected after a shadowing declaration.

```moonbit
test "resolve" {
  let a = @kernel.mk_tyvar("A")
  let st = @kernel.ks_add_const(@kernel.empty_kernel_state(), "c", a).unwrap()
  let ctx = @elab.elab_ctx_from_locals([("x", a)])
  let x = @elab.elab_resolve_name(st, ctx, "x").unwrap()
  let c = @elab.elab_resolve_name(st, ctx, "c").unwrap()
  inspect(@elab.rterm_to_string(c), content="RConst(c#1 : A <= A)")
  let eq = @elab.elab_resolve_eq(st, ctx, x, c).unwrap()
  inspect(@elab.elab_check_core_type(st, ctx, eq, @kernel.bool_ty()), content="true")
  inspect(@elab.elab_resolve_name(st, ctx, "nope") is Err(@elab.UnknownName("nope")), content="true")
  // a local named like a constant wins
  let ctx2 = @elab.elab_ctx_extend(ctx, "c", @kernel.bool_ty())
  inspect(@elab.elab_resolve_name(st, ctx2, "c") is Ok(@elab.RVar("c", _)), content="true")
}
```

## Core typing

### `elab_core_type_of`, `elab_check_core_type` and `rterm_well_formed`

`elab_core_type_of(state, ctx, t)` computes the type of a resolved term. A variable must be a local of `ctx` with the same type; a constant must still have the same identity and schema in `state`, and its type must be an instance of the schema. `elab_check_core_type` compares the result with an expected type, and `rterm_well_formed` tests that there is one.

```mbti
pub fn elab_core_type_of(@kernel.KernelState, ElabCtx, RTerm) -> @kernel.HolType?
pub fn elab_check_core_type(@kernel.KernelState, ElabCtx, RTerm, @kernel.HolType) -> Bool
pub fn rterm_well_formed(@kernel.KernelState, ElabCtx, RTerm) -> Bool
```

Core typing never looks a name up again: if the frozen identity is no longer the one in force, typing fails instead of picking up the new constant.

## Lowering

### `elab_lower_to_term` and `elab_lower_to_db`

`elab_lower_to_term` turns a resolved term into a kernel term, keeping every constant identity; `elab_lower_to_db` continues to the kernel's De Bruijn form.

```mbti
pub fn elab_lower_to_term(RTerm) -> Result[@kernel.Term, ElabError]
pub fn elab_lower_to_db(RTerm) -> Result[@kernel.DbTerm, ElabError]
```

Both fail with `CoreTypingFailure` when the lowered term is ill-typed or cannot be converted.

```moonbit
test "freeze" {
  let bool = @kernel.bool_ty()
  let st1 = @kernel.ks_add_const(@kernel.empty_kernel_state(), "c", bool).unwrap()
  let ctx = @elab.empty_elab_ctx()
  let c1 = @elab.elab_resolve_name(st1, ctx, "c").unwrap()
  // a shadowing declaration in an inner scope
  let st2 = @kernel.ks_add_const(@kernel.ks_push_scope(st1), "c", bool).unwrap()
  inspect(@elab.rterm_well_formed(st1, ctx, c1), content="true")
  inspect(@elab.rterm_well_formed(st2, ctx, c1), content="false")
  // the lowered term keeps the identity resolved in st1
  let t = @elab.elab_lower_to_term(c1).unwrap()
  inspect(@kernel.term_to_string(t), content="Const(c#1 : bool)")
  inspect(@elab.elab_roundtrip_term(st2, ctx, t) is Err(@elab.ScopeResolutionMismatch), content="true")
}
```

## Kernel term builders

These functions build kernel `Term` values directly, with a type check, for callers that do not need resolved terms.

### `elab_var`, `elab_const` and `elab_const_instance`

`elab_var` is `mk_var`. `elab_const` and `elab_const_instance` are `ks_mk_const` and `ks_mk_const_instance`.

```mbti
pub fn elab_var(String, @kernel.HolType) -> @kernel.Term
pub fn elab_const(@kernel.KernelState, String) -> Result[@kernel.Term, @kernel.SigError]
pub fn elab_const_instance(@kernel.KernelState, String, @kernel.HolType) -> Result[@kernel.Term, @kernel.SigError]
```

### `elab_app`, `elab_app2`, `elab_abs` and `elab_eq`

These functions build an application (of one or two arguments), an abstraction or an equation and fail with `TypeMismatch` when the result is ill-typed.

```mbti
pub fn elab_app(@kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn elab_app2(@kernel.Term, @kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn elab_abs(String, @kernel.HolType, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn elab_eq(@kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
```

### `elab_is_prop` and `elab_require_prop`

`elab_is_prop` tests whether a term is a well-typed proposition. `elab_require_prop` returns the term or fails with `NotBoolTerm` (or `TypeMismatch` when it is ill-typed).

```mbti
pub fn elab_is_prop(@kernel.Term) -> Bool
pub fn elab_require_prop(@kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
```

```moonbit
test "builders" {
  let a = @kernel.mk_tyvar("A")
  let f = @elab.elab_var("f", @kernel.fun_ty(a, @kernel.bool_ty()))
  let x = @elab.elab_var("x", a)
  let fx = @elab.elab_app(f, x).unwrap()
  inspect(@elab.elab_is_prop(fx), content="true")
  inspect(@elab.elab_app(x, f) is Err(@kernel.TypeMismatch), content="true")
  inspect(@elab.elab_require_prop(x) is Err(@kernel.NotBoolTerm), content="true")
}
```

## Errors

### `ElabError`

`ElabError` is the error of resolution and lowering.

```mbti
pub enum ElabError {
  UnknownName(String)
  UnknownConst(String)
  InvalidConstInstance(String)
  ScopeResolutionMismatch
  CoreTypingFailure
}
```

| Constructor | Meaning |
| --- | --- |
| `UnknownName(name)` | The name is neither a local nor a visible constant. |
| `UnknownConst(name)` | No constant with this name is declared. |
| `InvalidConstInstance(name)` | The requested type is not an instance of the constant's schema. |
| `ScopeResolutionMismatch` | A frozen identity no longer matches the state, or the state's tables disagree. |
| `CoreTypingFailure` | A resolved term is ill-typed in the current state and context. |

### `elab_err_unknown_name`, `elab_err_unknown_const`, `elab_err_invalid_const_instance`, `elab_err_scope_resolution_mismatch` and `elab_err_core_typing_failure`

These predicates test which constructor an `ElabError` is, for callers that prefer a function to a pattern.

```mbti
pub fn elab_err_unknown_name(ElabError) -> Bool
pub fn elab_err_unknown_const(ElabError) -> Bool
pub fn elab_err_invalid_const_instance(ElabError) -> Bool
pub fn elab_err_scope_resolution_mismatch(ElabError) -> Bool
pub fn elab_err_core_typing_failure(ElabError) -> Bool
```
