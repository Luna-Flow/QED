# elab design

The `elab` package fixes the meaning of every name in a term once, at elaboration time, and keeps that meaning when the signature later changes. This page explains the problem it solves, the two judgements it implements, and the stability property that makes it safe to resolve before the kernel checks anything.

## Design goal

Users write names; the kernel works with constant identities. Between the two sits a scoped signature in which `push`, `add` and `pop` change what a name refers to. The goal is a resolution step whose result does not change meaning behind the user's back: a term resolved in one scope either keeps exactly the constants it was resolved to, or fails, but never silently picks up a newer declaration with the same name.

## Mathematical background

The [formal specification](../../attachments/qed_formal_spec.typ) separates two judgements.

**Named elaboration** resolves a named term $t$ in a local context $\Gamma$ and a signature $\Sigma$ into a resolved term $d$:

$$
\Sigma ; \Gamma \vdash t \Downarrow d
$$

Its rules are: a name bound in $\Gamma$ becomes a variable; otherwise a name visible in $\Sigma$ becomes the constant $c^{\iota}_{\tau \preceq \sigma}$ with identity $\iota$, declared schema $\sigma$ and occurrence type $\tau$; applications and abstractions are resolved componentwise, with the binder added to $\Gamma$. The order "local, then constant" is fixed.

**Core typing** checks a resolved term without looking names up:

$$
\frac{(x : \tau) \in \Gamma}{\Sigma ; \Gamma \vdash_r x : \tau}
\qquad
\frac{\Sigma(\iota) = (c, \sigma) \quad \tau \preceq \sigma}{\Sigma ; \Gamma \vdash_r c^{\iota}_{\tau \preceq \sigma} : \tau}
\qquad
\frac{\Sigma;\Gamma \vdash_r f : \alpha \to \beta \quad \Sigma;\Gamma \vdash_r u : \alpha}{\Sigma;\Gamma \vdash_r f\,u : \beta}
$$

and the abstraction rule extends $\Gamma$. The constant rule reads $\Sigma(\iota)$, the declaration with identity $\iota$, not the declaration currently visible under the name $c$. In the implementation this is the check `id == rc.const_id && schema == rc.schema_ty` in `elab_core_type_of`.

## Design decisions

### Resolve once, freeze the identity

**Problem.** If a term stored names and looked them up whenever it was used, the same term could mean two different things before and after a scope change.

**Options.** Re-resolve on every use; store kernel terms only; store resolved terms with identities.

**Choice.** `RTerm` stores each constant as a `ResolvedConst` with its identity, schema and instance type. Core typing compares these with the state and fails on any difference.

**Why.** The specification's "Resolution Freeze under Scope Mutation" theorem states the property this buys: if $\Sigma; \Gamma \vdash t \Downarrow d$ and a sequence of push, add and pop operations turns $\Sigma$ into $\Sigma'$, then $d$ is unchanged, and every judgement about $d$ either still holds or fails visibly. The proof is that $d$ contains identities, not deferred lookups, and identities are never reused (the kernel allocates them from a monotone counter). Storing only kernel terms would also work for the kernel, but the frontend needs the schema to report instantiation errors and to check terms before lowering.

### Locals before constants

A local always shadows a constant of the same name. This is the usual lexical scoping, it is the rule the specification fixes, and it is the rule the tactic layer follows for hypothesis names versus theorem names. The examples in the [elab API](../api/elab.md) show a local `c` shadowing a constant `c`.

### A separate package

**Problem.** Resolution could live in the parser, which is its main client.

**Choice.** It is its own package between the kernel and the parser, depending only on the kernel.

**Why.** The resolution contract is part of the specification and is tested on its own; the parser can change its grammar without touching it, and other frontends can reuse it. The layering `kernel → logic/elab → parser` in [code governance](../code_governance.md) records this.

### Errors as data, typing as an option

Resolution returns `Result[_, ElabError]`; core typing returns `HolType?`. A failed lookup has a reason worth reporting (`UnknownName`, `InvalidConstInstance`), while a failed type check is a single fact (`CoreTypingFailure`) whose details the kernel would repeat anyway.

## Correctness and invariants

- **Soundness is not at stake.** `elab` builds terms, never theorems. A wrong resolution can only produce a term the kernel rejects or a theorem about a different statement than intended; the second is what freezing prevents.
- **Lowering preserves identities.** `elab_lower_to_term` maps $c^{\iota}_{\tau \preceq \sigma}$ to the kernel constant $c{:}\tau$ with identity $\iota$, so the kernel's admissibility check sees the identity the user resolved, and rejects a theorem whose constants have since been shadowed.
- **Round trip.** For a term $t$ built in state $\Sigma$, `elab_roundtrip_term(Σ', Γ, t)` succeeds exactly when re-resolving $t$ in $\Sigma'$ gives back the same identities, so it detects scope drift.
- **Equality is built in.** `=` resolves to identity `-1` with schema $\alpha \to \alpha \to \mathit{bool}$ in every state; it can be neither declared nor shadowed.

## Alternatives rejected

- **Lookup at kernel time.** Passing names to the kernel and letting it resolve would put scoping into the trusted base and make theorem meaning depend on the state at use.
- **Global unique names.** Requiring every constant name to be unique would remove shadowing and the need for identities, but the specification's scoped signature exists so that local developments can reuse names.
- **Type inference.** The resolver checks types that are written down; it does not infer types of binders or instantiate polymorphic constants from context.

## Boundaries

- No parsing: the [parser](parser.md) turns text into syntax and calls this package.
- No type inference or unification; every binder type is explicit and constants are used at their schema type unless an instance is requested.
- No overloading, coercions, implicit arguments or type classes.
- No theorems and no authority: lowering produces kernel terms only.
