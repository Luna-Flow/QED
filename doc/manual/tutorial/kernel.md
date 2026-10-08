# kernel tutorial

This tutorial proves theorems directly with the primitive rules of the `kernel` package. By the end you can build typed terms, derive new rules such as symmetry of equality from the ten primitives, declare and define constants, and see why a theorem cannot outlive the meaning of its constants. You do not need the `parser` or `prover` packages; everything here is plain MoonBit.

## Quick start

Add QED to your module and import the kernel in the `moon.pkg` of the package that uses it:

```bash
moon add Luna-Flow/QED@0.1.0
```

```text
import {
  "Luna-Flow/QED/kernel",
}
```

The smallest proof is one rule: REFL proves that any term equals itself.

```moonbit
test "quick start" {
  let st = @kernel.empty_kernel_state()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let th = @kernel.refl_checked(st, p).unwrap()
  inspect(
    @kernel.thm_to_string(th),
    content="[] |- Comb(Comb(Const(= : fun(bool, fun(bool, bool))), FVar(p : bool)), FVar(p : bool))",
  )
}
```

The output reads $\vdash p = p$: no hypotheses (`[]`), and a conclusion that applies the equality constant `=` at type $\mathit{bool} \to \mathit{bool} \to \mathit{bool}$ to `p` twice. `thm_to_string` prints the De Bruijn form the kernel works on, so free variables appear as `FVar`.

Every rule takes a `KernelState` first. The empty state knows the types `bool`, `ind` and `fun`, the built-in equality and the choice constant `@`.

## Everyday tasks

### Build and type-check terms

Terms are built with `mk_var`, `mk_comb`, `mk_abs` and `mk_eq`; nothing is checked until you ask for a type or use the term in a rule.

```moonbit
test "build terms" {
  let a = @kernel.mk_tyvar("A")
  let f = @kernel.mk_var("f", @kernel.fun_ty(a, a))
  let x = @kernel.mk_var("x", a)
  let fx = @kernel.mk_comb(f, x)
  inspect(@kernel.hol_type_to_string(@kernel.type_of(fx).unwrap()), content="A")
  // λx. f x has type A -> A
  let lam = @kernel.mk_abs(x, fx)
  inspect(@kernel.hol_type_to_string(@kernel.type_of(lam).unwrap()), content="fun(A, A)")
  // f applied to itself is ill-typed
  inspect(@kernel.type_of(@kernel.mk_comb(f, f)) is None, content="true")
  // α-equivalence ignores the name of the bound variable
  let y = @kernel.mk_var("y", a)
  inspect(@kernel.term_alpha_eq(lam, @kernel.mk_abs(y, @kernel.mk_comb(f, y))), content="true")
}
```

### Use hypotheses

ASSUME introduces a hypothesis, and EQ_MP uses an equation between propositions to move a proof from one side to the other. Together they prove $\{p = q, p\} \vdash q$.

```moonbit
test "hypotheses" {
  let st = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let th_eq = @kernel.assume_checked(st, @kernel.mk_eq(p, q).unwrap()).unwrap() // {p = q} |- p = q
  let th_p = @kernel.assume_checked(st, p).unwrap() // {p} |- p
  let th_q = @kernel.eq_mp_checked(st, th_eq, th_p).unwrap() // {p = q, p} |- q
  inspect(@kernel.thm_hyp_count(th_q), content="2")
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_q).unwrap()), content="Var(q : bool)")
  // EQ_MP checks that the second theorem proves the left-hand side
  inspect(@kernel.eq_mp_checked(st, th_eq, th_eq) is Err(@kernel.AlphaMismatch), content="true")
}
```

### Derive symmetry of equality

The kernel has no symmetry rule. It is derivable, and deriving it shows how larger rules are built from the primitives. From $\Gamma \vdash s = t$:

$$
\begin{aligned}
&\vdash (=) = (=) && \textsf{REFL} \\
&\Gamma \vdash (=)\,s = (=)\,t && \textsf{MK\_COMB} \text{ with the premise} \\
&\Gamma \vdash (s = s) = (t = s) && \textsf{MK\_COMB} \text{ with } \vdash s = s \\
&\Gamma \vdash t = s && \textsf{EQ\_MP} \text{ with } \vdash s = s
\end{aligned}
$$

```moonbit
fn sym(st : @kernel.KernelState, th : @kernel.Thm) -> @kernel.Thm raise @kernel.LogicError {
  let (s, _) = @kernel.dest_eq(@kernel.thm_concl(th).unwrap_or_error()).unwrap_or_error()
  let ty = @kernel.type_of(s).unwrap()
  let eq = @kernel.mk_const("=", @kernel.fun_ty(ty, @kernel.fun_ty(ty, @kernel.bool_ty())))
  let refl_eq = @kernel.refl_checked(st, eq).unwrap_or_error()
  let th1 = @kernel.mk_comb_rule_checked(st, refl_eq, th).unwrap_or_error()
  let refl_s = @kernel.refl_checked(st, s).unwrap_or_error()
  let th2 = @kernel.mk_comb_rule_checked(st, th1, refl_s).unwrap_or_error()
  @kernel.eq_mp_checked(st, th2, refl_s).unwrap_or_error()
}

test "derived symmetry" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let th = @kernel.assume_checked(st, @kernel.mk_eq(x, y).unwrap()).unwrap() // {x = y} |- x = y
  let flipped = sym(st, th) // {x = y} |- y = x
  let (l, r) = @kernel.dest_eq(@kernel.thm_concl(flipped).unwrap()).unwrap()
  inspect(@kernel.term_to_string(l) + " = " + @kernel.term_to_string(r), content="Var(y : A) = Var(x : A)")
  inspect(@kernel.thm_hyp_count(flipped), content="1")
  // a premise that is not an equation makes sym raise
  let not_eq = @kernel.assume_checked(st, @kernel.mk_var("p", @kernel.bool_ty())).unwrap()
  let r = try sym(st, not_eq) catch { e => Err(e) } noraise { th => Ok(th) }
  inspect(r is Err(@kernel.NotAnEquality), content="true")
}
```

`unwrap_or_error` turns an `Err` into a raised `LogicError`, so `sym` fails cleanly, with `NotAnEquality`, when its premise is not an equation. Every intermediate theorem was checked by the kernel; `sym` itself needs no trust. The `logic` package ships this rule as `logic_eq_sym`.

### Compute with β-reduction and abstraction

BETA proves a redex equal to its contraction, and ABS lifts an equation under a binder as long as the bound variable is not free in a hypothesis.

```moonbit
test "beta and abs" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let k = @kernel.mk_abs(x, @kernel.mk_abs(y, x)) // λx. λy. x
  // BETA: (λx. λy. x) y = λ_. y; the inner binder is renamed, not captured
  let th = @kernel.beta_rule_checked(st, @kernel.mk_comb(k, y)).unwrap()
  let (_, rhs) = @kernel.dest_eq(@kernel.thm_concl(th).unwrap()).unwrap()
  inspect(@kernel.term_to_string(rhs), content="Abs(Var(_b0 : A), Var(y : A))")
  // ABS over x: |- λx. x = λx. x from |- x = x
  let th_abs = @kernel.abs_rule_checked(st, x, @kernel.refl_checked(st, x).unwrap()).unwrap()
  inspect(@kernel.thm_hyp_count(th_abs), content="0")
  // but not over a variable that a hypothesis mentions
  let th_h = @kernel.assume_checked(st, @kernel.mk_eq(x, y).unwrap()).unwrap()
  inspect(@kernel.abs_rule_checked(st, x, th_h) is Err(@kernel.VarFreeInHyp), content="true")
}
```

### Declare constants and watch scopes

Constants live in a scoped signature. A theorem records which declaration each of its constants refers to, and the kernel refuses to use it where that declaration is not the one in force.

```moonbit
test "scopes" {
  let st0 = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let st1 = @kernel.ks_add_const(st0, "c", bool).unwrap()
  let c = @kernel.ks_mk_const(st1, "c").unwrap()
  let th = @kernel.refl_checked(st1, c).unwrap() // |- c = c, about c#1
  // an inner scope declares another c
  let st2 = @kernel.ks_add_const(@kernel.ks_push_scope(st1), "c", bool).unwrap()
  inspect(@kernel.thm_is_admissible(st2, th), content="false")
  inspect(@kernel.trans_checked(st2, th, th) is Err(@kernel.InvalidInstantiation), content="true")
  // after popping the scope the theorem is usable again
  let st3 = @kernel.ks_pop_scope(st2).unwrap()
  inspect(@kernel.trans_checked(st3, th, th) is Ok(_), content="true")
}
```

### Define a constant

A definition introduces a constant together with its defining theorem. The gate checks that the definition cannot make the theory inconsistent.

```moonbit
test "define" {
  let st0 = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let x = @kernel.mk_var("x", bool)
  let (st1, def_th) = @kernel.ks_define_const_thm(
    st0,
    "id_bool",
    @kernel.fun_ty(bool, bool),
    @kernel.mk_abs(x, x),
  ).unwrap()
  // |- id_bool = λx. x
  let (lhs, _) = @kernel.dest_eq(@kernel.thm_concl(def_th).unwrap()).unwrap()
  inspect(@kernel.term_to_string(lhs), content="Const(id_bool#1 : fun(bool, bool))")
  // the definition is recorded for audit
  let (gate, heads, _) = @kernel.ks_extension_cert_at(st1, 0).unwrap()
  inspect(gate is @kernel.DefOK && heads == ["id_bool"], content="true")
  // a right-hand side with a free variable is refused
  inspect(@kernel.ks_define_const(st0, "bad", bool, x) is Err(@kernel.DefinitionNotClosed), content="true")
}
```

## Going further

**Build derived rules as functions.** `sym` above is the pattern for every derived rule: a MoonBit function from theorems to a theorem that calls primitive rules and propagates their errors, by returning a `Result` or by raising with `unwrap_or_error`. The `logic` package is a library of such functions: `logic_eq_sym`, `logic_apply_fun_eq`, `logic_beta_normalize_eq`, and the propositional rules in the [logic API](../api/logic.md). Write yours the same way and you need not review them for soundness, only for usefulness.

**Instantiate.** INST_TYPE and INST specialise a general theorem. A theorem proved for a type variable `A` holds at every type the state admits:

```moonbit
test "instantiate" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let th = @kernel.refl_checked(st, x).unwrap() // |- x = x  at A
  let th_bool = @kernel.inst_type(st, [("A", @kernel.bool_ty())], th).unwrap()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let x_bool = @kernel.mk_var("x", @kernel.bool_ty())
  let th_p = @kernel.inst_checked(st, [(x_bool, p)], th_bool).unwrap() // |- p = p
  inspect(@kernel.term_alpha_eq(@kernel.thm_concl(th_p).unwrap(), @kernel.mk_eq(p, p).unwrap()), content="true")
  // a type the state does not know is refused
  let bad = @kernel.inst_type(st, [("A", @kernel.mk_tyapp("nat", []))], th)
  inspect(bad is Err(@kernel.InvalidInstantiation), content="true")
}
```

**Extend the theory.** `ks_register_type_definition` adds a new type from a non-empty subset of an existing one, and `ks_specify_const` adds a constant characterised by a property, given a witness. Both are shown on the [kernel API](../api/kernel.md) page. Keep the state before an extension: `ks_conservative_replay_ok(base, extended, th)` checks that a theorem proved after the extension but stated in the old language is still a theorem of the old theory.

**Work with errors.** All failures are values of `LogicError` or `SigError`. Match them with `is` to react to a specific failure, or propagate them with `unwrap_or_error` from a function that raises `LogicError`.

**Go up a layer.** Writing proofs rule by rule is how the kernel is tested, not how proofs are meant to be written. The [tactics tutorial](tactics.md) works backwards from goals, and the [prover tutorial](prover.md) runs theorem scripts that are checked by exactly the rules shown here.

## Common pitfalls

- **Comparing terms structurally.** Terms read back from a theorem have generated binder names such as `_b0`. Compare them with `term_alpha_eq`, or `term_logical_eq` when constant identities may differ, never with `term_to_string`.
- **Building constants with `mk_const`.** `mk_const` leaves the constant unresolved, and a rule rejects a constant the state does not declare (`TypeMismatch`). Use `ks_mk_const` or `ks_mk_const_instance`, which take the identity and schema from the state. The equality constant `=` is the exception: it is built in.
- **Reusing a binder name at another type.** `mk_abs(mk_var("x", A), mk_var("x", B))` is rejected at the De Bruijn boundary (`BoundaryFailure`). Use distinct names.
- **Using a theorem across states.** A theorem is checked against the state passed to each rule. After shadowing a constant, older theorems about the outer constant fail with `InvalidInstantiation` until the scope is popped.
- **Assuming a non-proposition.** ASSUME, ADD_ASSUM and EQ_MP need terms of type `bool`; they return `NotBoolTerm` otherwise.
- **Expecting `unwrap` to be safe.** The examples use `unwrap` for brevity. Library code should match on the `Result`.

## Next steps

- The [kernel API](../api/kernel.md) lists every function with its exact failure cases.
- The [kernel design](../design/kernel.md) explains why these rules are sound and why the theorem type is abstract.
- The [logic tutorial](logic.md) builds propositional connectives on top of the kernel.
- The [formal specification](../../attachments/qed_formal_spec.typ) is the normative definition of every rule.
