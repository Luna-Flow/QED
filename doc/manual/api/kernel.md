# kernel API

## Purpose

The `kernel` package (`Luna-Flow/QED/kernel`) is the trusted kernel of QED. It defines HOL types and terms, the abstract theorem type `Thm`, the primitive inference rules that are the only way to build a `Thm`, the scoped signature, and the three extension gates `DefOK`, `TypeDefOK` and `SpecOK`. It depends on no other QED package. Every other package reaches theorems only through the functions on this page.

Failures are values: rules return `Result[Thm, LogicError]` and signature operations return `Result[_, SigError]`. Nothing on this page aborts on bad input.

The meaning of the rules is explained in the [kernel design](../design/kernel.md); a guided walk is in the [kernel tutorial](../tutorial/kernel.md). The normative definitions are in the formal specification:

[QED formal specification](../../attachments/qed_formal_spec.typ)

## Importing

Add the package to your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/QED/kernel",
}
```

The examples on this page are blackbox tests that refer to this package as `@kernel`.

## Types

### `HolType`

`HolType` is a simple type: a type variable or a type constructor applied to arguments.

```mbti
pub enum HolType {
  TyVal(String)
  TyApp(String, Array[HolType])
}
```

`TyVal(a)` is the type variable $\alpha$ named `a`. `TyApp(c, args)` applies the constructor `c` to `args`. The built-in constructors are `bool` (arity 0), `ind` (arity 0) and `fun` (arity 2); `fun(a, b)` is the function type $a \to b$. Other constructors become usable only after `ks_register_type_definition` admits them. The enum is read-only outside the package: match on it, but build values with the functions below.

### `mk_tyvar`

`mk_tyvar` builds the type variable with the given name.

```mbti
pub fn mk_tyvar(String) -> HolType
```

### `mk_tyapp`

`mk_tyapp` applies a type constructor to an argument list.

```mbti
pub fn mk_tyapp(String, Array[HolType]) -> HolType
```

The result is not checked against the signature. `ks_type_is_admissible` decides whether a state accepts it.

### `bool_ty`, `ind_ty` and `fun_ty`

These functions build the three built-in types: `bool_ty()` is `bool`, `ind_ty()` is the infinite individuals type `ind`, and `fun_ty(a, b)` is $a \to b$.

```mbti
pub fn bool_ty() -> HolType
pub fn ind_ty() -> HolType
pub fn fun_ty(HolType, HolType) -> HolType
```

### `dest_tyapp` and `dest_fun_ty`

`dest_tyapp` returns the constructor and arguments of a type application, and `dest_fun_ty` returns the domain and codomain of a function type. Both return `None` on any other shape.

```mbti
pub fn dest_tyapp(HolType) -> (String, Array[HolType])?
pub fn dest_fun_ty(HolType) -> (HolType, HolType)?
```

### `is_bool_ty`, `is_tyvar` and `is_tyapp`

These predicates test the shape of a type.

```mbti
pub fn is_bool_ty(HolType) -> Bool
pub fn is_tyvar(HolType) -> Bool
pub fn is_tyapp(HolType) -> Bool
```

### `ty_eq`

`ty_eq` is structural equality of types.

```mbti
pub fn ty_eq(HolType, HolType) -> Bool
```

### `tyvars` and `tyvars_subset`

`tyvars` lists the type variables of a type without duplicates, in order of first occurrence. `tyvars_subset(a, b)` holds when every type variable of `a` occurs in `b`.

```mbti
pub fn tyvars(HolType) -> Array[String]
pub fn tyvars_subset(HolType, HolType) -> Bool
```

### `ty_is_instance_of`

`ty_is_instance_of(instance, schema)` holds when some type substitution $\theta$ maps `schema` to `instance`, that is $\mathit{schema}\,\theta = \mathit{instance}$.

```mbti
pub fn ty_is_instance_of(HolType, HolType) -> Bool
```

Note the argument order: the instance comes first. The kernel uses this relation to check every occurrence of a polymorphic constant against its declared schema.

### `type_subst`, `type_subst_unsafe` and `has_duplicate_ty_subst_keys`

`type_subst(theta, ty)` applies the type substitution `theta`, given as pairs of a type-variable name and a type, to `ty`. It returns `None` when `theta` names a variable twice, which `has_duplicate_ty_subst_keys` tests. `type_subst_unsafe` skips that check and uses the first binding of a repeated name.

```mbti
pub fn type_subst(Array[(String, HolType)], HolType) -> HolType?
pub fn type_subst_unsafe(Array[(String, HolType)], HolType) -> HolType
pub fn has_duplicate_ty_subst_keys(Array[(String, HolType)]) -> Bool
```

### `hol_type_to_string`

`hol_type_to_string` renders a type for tests and diagnostics: `A`, `bool`, `fun(A, bool)`.

```mbti
pub fn hol_type_to_string(HolType) -> String
```

```moonbit
test "types" {
  let a = @kernel.mk_tyvar("A")
  let pred = @kernel.fun_ty(a, @kernel.bool_ty())
  inspect(@kernel.hol_type_to_string(pred), content="fun(A, bool)")
  inspect(@kernel.dest_fun_ty(pred) is Some((_, cod)) && @kernel.is_bool_ty(cod), content="true")
  assert_eq(@kernel.tyvars(pred), ["A"])
  let inst = @kernel.type_subst([("A", @kernel.ind_ty())], pred).unwrap()
  inspect(@kernel.hol_type_to_string(inst), content="fun(ind, bool)")
  inspect(@kernel.ty_is_instance_of(inst, pred), content="true")
  inspect(@kernel.ty_is_instance_of(pred, inst), content="false")
  inspect(@kernel.type_subst([("A", a), ("A", a)], pred) is None, content="true")
}
```

## Terms

### `Term`

`Term` is a named term of the simply typed λ-calculus.

```mbti
pub enum Term {
  Var(String, HolType)
  Const(String, HolType, Int)
  Comb(Term, Term)
  Abs(Term, Term)
}
```

`Var(x, ty)` is a variable; two variables are the same only when both the name and the type agree. `Const(c, ty, id)` is an occurrence of the constant `c` at the type `ty`; `id` is the constant identity (`ConstId`) the occurrence was resolved to, or `-1` when it has not been resolved. `Comb(f, x)` is the application $f\,x$ and `Abs(v, body)` is the abstraction $\lambda v.\,\mathit{body}$, whose binder `v` must be a `Var`. The enum is read-only outside the package.

### `mk_var`, `mk_const`, `mk_const_bound`, `mk_comb` and `mk_abs`

These functions build terms without checking them. `mk_const` leaves the constant identity unresolved (`-1`); `mk_const_bound` sets it explicitly.

```mbti
pub fn mk_var(String, HolType) -> Term
pub fn mk_const(String, HolType) -> Term
pub fn mk_const_bound(String, HolType, Int) -> Term
pub fn mk_comb(Term, Term) -> Term
pub fn mk_abs(Term, Term) -> Term
```

A term built here may be ill-typed. `type_of` checks it, and every rule rejects ill-typed input. Prefer `ks_mk_const` and `ks_mk_const_instance`, which take the type and the identity from the signature.

### `is_var`, `is_const`, `is_comb` and `is_abs`

These predicates test the outermost constructor of a term.

```mbti
pub fn is_var(Term) -> Bool
pub fn is_const(Term) -> Bool
pub fn is_comb(Term) -> Bool
pub fn is_abs(Term) -> Bool
```

### `dest_var`, `dest_const`, `dest_comb` and `dest_abs`

These functions take a term apart, or return `None` on another shape. `dest_const` drops the constant identity.

```mbti
pub fn dest_var(Term) -> (String, HolType)?
pub fn dest_const(Term) -> (String, HolType)?
pub fn dest_comb(Term) -> (Term, Term)?
pub fn dest_abs(Term) -> (Term, Term)?
```

### `type_of`

`type_of` computes the type of a term, or returns `None` when the term is ill-typed.

```mbti
pub fn type_of(Term) -> HolType?
```

It implements the typing rules of the simply typed λ-calculus:

$$
\frac{}{x{:}\tau \vdash x : \tau}
\qquad
\frac{f : \sigma \to \tau \quad x : \sigma}{f\,x : \tau}
\qquad
\frac{t : \tau}{\lambda (x{:}\sigma).\,t : \sigma \to \tau}
$$

Constants have the type written on the occurrence. The cost is linear in the size of the term.

### `mk_eq` and `dest_eq`

`mk_eq(l, r)` builds the equation $l = r$, using the built-in constant `=` at the type $\tau \to \tau \to \mathit{bool}$. `dest_eq` takes an equation apart.

```mbti
pub fn mk_eq(Term, Term) -> Result[Term, LogicError]
pub fn dest_eq(Term) -> Result[(Term, Term), LogicError]
```

`mk_eq` fails with `TypeMismatch` when a side is ill-typed or the two types differ, and with `BoundaryFailure` when a side cannot be converted to De Bruijn form (see `to_db_term`). `dest_eq` fails with `NotAnEquality` when the term is not an application of `=` to two arguments, and with `TypeMismatch` when the equation is ill-typed.

### `free_vars`, `term_is_closed` and `term_has_const_named`

`free_vars` lists the free variables of a term as name and type pairs, without duplicates. `term_is_closed` holds when there are none. `term_has_const_named` tests whether a constant with the given name occurs anywhere in the term.

```mbti
pub fn free_vars(Term) -> Array[(String, HolType)]
pub fn term_is_closed(Term) -> Bool
pub fn term_has_const_named(Term, String) -> Bool
```

### `term_tyvars` and `term_tyvars_subset`

`term_tyvars` lists the type variables that occur anywhere in a term. `term_tyvars_subset(t, ty)` holds when every type variable of `t` occurs in `ty`; the definition gate uses it to reject ghost type variables.

```mbti
pub fn term_tyvars(Term) -> Array[String]
pub fn term_tyvars_subset(Term, HolType) -> Bool
```

### `term_apply_ty_subst` and `term_apply_ty_subst_unsafe`

These functions apply a type substitution to every type inside a term. The checked form returns `None` when a type variable is named twice.

```mbti
pub fn term_apply_ty_subst(Array[(String, HolType)], Term) -> Term?
pub fn term_apply_ty_subst_unsafe(Array[(String, HolType)], Term) -> Term
```

### `term_alpha_eq` and `term_logical_eq`

`term_alpha_eq` decides α-equivalence: the terms are equal after renaming bound variables. It compares the De Bruijn forms, including constant identities. `term_logical_eq` is the same comparison but ignores constant identities, so an unresolved occurrence of `c` equals a resolved one. Both return `false` when a term cannot be converted to De Bruijn form.

```mbti
pub fn term_alpha_eq(Term, Term) -> Bool
pub fn term_logical_eq(Term, Term) -> Bool
```

### `term_to_string`

`term_to_string` renders a named term structurally, for tests and diagnostics.

```mbti
pub fn term_to_string(Term) -> String
```

```moonbit
test "terms" {
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let id_x = @kernel.mk_abs(x, x)
  let id_y = @kernel.mk_abs(y, y)
  inspect(@kernel.hol_type_to_string(@kernel.type_of(id_x).unwrap()), content="fun(A, A)")
  inspect(@kernel.term_alpha_eq(id_x, id_y), content="true")
  inspect(@kernel.free_vars(@kernel.mk_comb(id_x, y)).length(), content="1")
  // applying a function of type A -> A to a bool is ill-typed
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  inspect(@kernel.type_of(@kernel.mk_comb(id_x, p)) is None, content="true")
  let eq = @kernel.mk_eq(x, y).unwrap()
  inspect(
    @kernel.term_to_string(eq),
    content="Comb(Comb(Const(= : fun(A, fun(A, bool))), Var(x : A)), Var(y : A))",
  )
  inspect(@kernel.mk_eq(x, p) is Err(@kernel.TypeMismatch), content="true")
  inspect(@kernel.dest_eq(p) is Err(@kernel.NotAnEquality), content="true")
}
```

## De Bruijn terms

The rules run on a typed De Bruijn representation, so α-equivalent terms are literally equal there. These functions expose that representation for audits and tests.

### `DbTerm`

`DbTerm` is a term with De Bruijn indices for bound variables.

```mbti
pub enum DbTerm {
  DbBound(Int, HolType)
  DbFree(String, HolType)
  DbConst(String, HolType, Int)
  DbComb(DbTerm, DbTerm)
  DbAbs(HolType, DbTerm)
}
```

`DbBound(i, ty)` refers to the binder `i` levels up, counting from 0. Each bound occurrence keeps its type, and `DbAbs(ty, body)` keeps the binder type, so the representation is typed.

### `to_db_term` and `from_db_term`

`to_db_term` converts a named term to De Bruijn form; `from_db_term` converts back, choosing fresh binder names `_b0`, `_b1`, ... that avoid the free names of the term.

```mbti
pub fn to_db_term(Term) -> DbTerm?
pub fn from_db_term(DbTerm) -> Term?
```

`to_db_term` returns `None` when an abstraction binder is not a variable, or when a variable has the name of an enclosing binder but a different type, as in $\lambda (x{:}A).\,(x{:}B)$. QED rejects such terms instead of reading the inner `x` as a separate free variable. `from_db_term` returns `None` on a dangling index or a type label that disagrees with its binder. On success, `from_db_term(to_db_term(t))` is α-equivalent to `t`.

### `db_term_eq`, `db_type_of` and `db_term_to_string`

`db_term_eq` is structural equality of De Bruijn terms, including constant identities; on converted terms it decides α-equivalence. `db_type_of` is `type_of` for De Bruijn terms. `db_term_to_string` renders one, as `thm_to_string` does.

```mbti
pub fn db_term_eq(DbTerm, DbTerm) -> Bool
pub fn db_type_of(DbTerm) -> HolType?
pub fn db_term_to_string(DbTerm) -> String
```

### `db_has_free`

`db_has_free(t, v)` tests whether the free variable `v` (a `DbFree`) occurs in `t`.

```mbti
pub fn db_has_free(DbTerm, DbTerm) -> Bool
```

### `db_subst_free_parallel`

`db_subst_free_parallel(t, sigma)` replaces every free variable that is a key of `sigma` by its value, simultaneously. Values are shifted under binders, so no capture can happen. It returns `None` only when an index computation would overflow.

```mbti
pub fn db_subst_free_parallel(DbTerm, Array[(DbTerm, DbTerm)]) -> DbTerm?
```

### `db_apply_ty_subst`

`db_apply_ty_subst` applies a type substitution to every type label of a De Bruijn term.

```mbti
pub fn db_apply_ty_subst(Array[(String, HolType)], DbTerm) -> DbTerm
```

### `db_beta_reduce_once`

`db_beta_reduce_once` contracts a top-level β-redex $(\lambda.\,t)\,u$ and returns `None` on any other shape.

```mbti
pub fn db_beta_reduce_once(DbTerm) -> DbTerm?
```

The contraction is $\uparrow^{-1}_0\big(t[0 \mapsto \uparrow^{1}_0 u]\big)$: shift `u` up, substitute it for index 0, shift the result down. The [kernel design](../design/kernel.md) derives why this avoids capture.

```moonbit
test "de bruijn" {
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let k = @kernel.mk_abs(x, @kernel.mk_abs(y, x)) // λx. λy. x
  let db = @kernel.to_db_term(k).unwrap()
  inspect(@kernel.db_term_to_string(db), content="Abs(A. Abs(A. BVar(1 : A)))")
  // (λx. λy. x) y  reduces to  λ_b. y, not to λy. y
  let redex = @kernel.to_db_term(@kernel.mk_comb(k, y)).unwrap()
  let out = @kernel.db_beta_reduce_once(redex).unwrap()
  inspect(@kernel.db_term_to_string(out), content="Abs(A. FVar(y : A))")
  inspect(
    @kernel.term_to_string(@kernel.from_db_term(out).unwrap()),
    content="Abs(Var(_b0 : A), Var(y : A))",
  )
  // a binder name reused at another type is rejected
  let x_bool = @kernel.mk_var("x", @kernel.bool_ty())
  inspect(@kernel.to_db_term(@kernel.mk_abs(x, x_bool)) is None, content="true")
}
```

## Theorems

### `Thm`

`Thm` is the abstract type of theorems: a sequent $\Gamma \vdash p$ with a finite set of hypotheses $\Gamma$ and a conclusion $p$, all of type `bool`.

```mbti
type Thm
```

The type is abstract: no code outside the package can build or change a `Thm`. A value of type `Thm` exists only because a primitive rule or an extension gate produced it, and that is the whole basis of the trust argument in the [kernel design](../design/kernel.md). Hypotheses are kept as a set of α-equivalence classes: duplicates up to α-equivalence are merged. The comparison also looks at constant identity stamps, so a hypothesis built with `mk_const` and the same hypothesis built with `ks_mk_const` stay two entries, and DEDUCT_ANTISYM_RULE does not discharge one with the other. Build the terms of one proof the same way, preferably with `ks_mk_const`.

### `thm_hyps`, `thm_concl` and `thm_hyp_count`

`thm_hyps` returns the hypotheses and `thm_concl` the conclusion, as named terms. `thm_hyp_count` returns the number of hypotheses.

```mbti
pub fn thm_hyps(Thm) -> Result[Array[Term], LogicError]
pub fn thm_concl(Thm) -> Result[Term, LogicError]
pub fn thm_hyp_count(Thm) -> Int
```

Bound variables come back with canonical names (`_b0`, ...), so compare results with `term_alpha_eq` or `term_logical_eq`, not structurally. The `Err(BoundaryFailure)` case cannot occur for a theorem built by the kernel.

### `thm_to_string`

`thm_to_string` renders a theorem as `[h1, h2] |- c` in De Bruijn form.

```mbti
pub fn thm_to_string(Thm) -> String
```

### `thm_is_admissible` and `thm_bind_const_ids`

`thm_is_admissible(state, th)` holds when `th` is acceptable in `state`: every constant it mentions is declared there with the identity recorded in the theorem, every constant occurrence is an instance of its declared schema, every type is admissible, and a definition theorem still matches its definition. `thm_bind_const_ids` resolves the constants of `th` again in `state`, records the identities it finds and then checks admissibility. An occurrence that carries an identity stamp keeps it; an occurrence built with `mk_const` (stamp $-1$) takes whatever the name means in `state`, even if the theorem recorded another identity for it.

```mbti
pub fn thm_is_admissible(KernelState, Thm) -> Bool
pub fn thm_bind_const_ids(KernelState, Thm) -> Result[Thm, LogicError]
```

Every checked rule runs this check on its premises and on its result, so a theorem proved before a scope change cannot be used after the change made one of its constants mean something else. `thm_bind_const_ids` is the exception: it can move a theorem about an outer constant `c`, written with unstamped occurrences, to a constant `c` declared by an inner scope. This is sound, because only constants without a definition can be shadowed, and the [kernel design](../design/kernel.md) explains why; but the result is about the inner constant. `thm_bind_const_ids` fails with `InvalidInstantiation` when a stamped identity disagrees with the state and with `TypeMismatch` when a constant is unknown.

## Primitive rules

Each rule takes the kernel state first, checks that its premise theorems are admissible in that state, applies the rule and checks the result. In the rules below $\Gamma, \Delta$ are hypothesis sets, $\equiv_\alpha$ is α-equivalence (constant identities ignored), and $\setminus$ removes every hypothesis α-equivalent to the given term whose constants carry the same identity stamps (see `Thm` above). The [kernel design](../design/kernel.md) explains why each rule is sound.

### `refl_checked`

`refl_checked` is REFL: it proves that a term equals itself.

```mbti
pub fn refl_checked(KernelState, Term) -> Result[Thm, LogicError]
```

$$
\frac{}{\vdash t = t}\;\textsf{REFL}
$$

Fails with `TypeMismatch` when `t` is ill-typed or mentions a constant the state does not declare, and with `BoundaryFailure` when `t` cannot be converted to De Bruijn form.

### `assume_checked`

`assume_checked` is ASSUME: it proves a proposition from itself.

```mbti
pub fn assume_checked(KernelState, Term) -> Result[Thm, LogicError]
```

$$
\frac{p : \mathit{bool}}{\{p\} \vdash p}\;\textsf{ASSUME}
$$

Fails with `NotBoolTerm` when `p` is well-typed but not of type `bool`.

### `add_assum_checked`

`add_assum_checked(state, q, th)` adds the proposition `q` to the hypotheses of `th` (weakening).

```mbti
pub fn add_assum_checked(KernelState, Term, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash p \qquad q : \mathit{bool}}{\Gamma \cup \{q\} \vdash p}\;\textsf{ADD\_ASSUM}
$$

Weakening is not among the ten rules of the specification; it is derivable from ASSUME, DEDUCT_ANTISYM_RULE and EQ_MP, and the [kernel design](../design/kernel.md) gives the derivation. Fails with `NotBoolTerm` when `q` is not a proposition.

### `trans_checked`

`trans_checked` is TRANS: it chains two equations.

```mbti
pub fn trans_checked(KernelState, Thm, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash s = t \qquad \Delta \vdash t' = u \qquad t \equiv_\alpha t'}{\Gamma \cup \Delta \vdash s = u}\;\textsf{TRANS}
$$

Fails with `NotAnEquality` when a premise is not an equation and with `AlphaMismatch` when the middle terms differ.

### `mk_comb_rule_checked`

`mk_comb_rule_checked` is MK_COMB: equal functions applied to equal arguments give equal results.

```mbti
pub fn mk_comb_rule_checked(KernelState, Thm, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash f = g \qquad \Delta \vdash x = y}{\Gamma \cup \Delta \vdash f\,x = g\,y}\;\textsf{MK\_COMB}
$$

Fails with `TypeMismatch` unless $f, g : \sigma \to \tau$ and $x, y : \sigma$.

### `abs_rule_checked`

`abs_rule_checked(state, x, th)` is ABS: it abstracts both sides of an equation over a variable.

```mbti
pub fn abs_rule_checked(KernelState, Term, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash s = t \qquad x \notin \mathrm{FV}(\Gamma)}{\Gamma \vdash (\lambda x.\,s) = (\lambda x.\,t)}\;\textsf{ABS}
$$

Fails with `VarFreeInHyp` when `x` occurs free in a hypothesis, with `InvalidInstantiation` when `x` is not a variable, and with `NotAnEquality` when the premise is not an equation.

### `beta_rule_checked`

`beta_rule_checked` is BETA: it proves a β-redex equal to its contraction.

```mbti
pub fn beta_rule_checked(KernelState, Term) -> Result[Thm, LogicError]
```

$$
\frac{u : \sigma}{\vdash (\lambda (x{:}\sigma).\,t)\,u = t[u/x]}\;\textsf{BETA}
$$

The substitution is capture-avoiding because it runs on De Bruijn terms. Fails with `NotTrivialBetaRedex` when the term is not an application of an abstraction, and with `TypeMismatch` when the argument type differs from the binder type.

### `eq_mp_checked`

`eq_mp_checked` is EQ_MP: an equation between propositions transports a proof of the left side to the right side.

```mbti
pub fn eq_mp_checked(KernelState, Thm, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash p = q \qquad \Delta \vdash p' \qquad p \equiv_\alpha p'}{\Gamma \cup \Delta \vdash q}\;\textsf{EQ\_MP}
$$

Fails with `NotBoolTerm` when the sides are not propositions and with `AlphaMismatch` when the second premise does not prove the left side.

### `deduct_antisym_rule_checked`

`deduct_antisym_rule_checked` is DEDUCT_ANTISYM_RULE: two propositions that prove each other are equal.

```mbti
pub fn deduct_antisym_rule_checked(KernelState, Thm, Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash p \qquad \Delta \vdash q}{(\Gamma \setminus \{q\}) \cup (\Delta \setminus \{p\}) \vdash p = q}\;\textsf{DEDUCT\_ANTISYM\_RULE}
$$

Fails with `NotBoolTerm` when a conclusion is not a proposition.

### `inst_type`

`inst_type(state, theta, th)` is INST_TYPE: it instantiates type variables throughout a theorem.

```mbti
pub fn inst_type(KernelState, Array[(String, HolType)], Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash p}{\Gamma\theta \vdash p\theta}\;\textsf{INST\_TYPE}
$$

Fails with `InvalidInstantiation` when `theta` names a variable twice or maps to a type the state does not admit, and with `TypeMismatch` when an instantiated constant is no longer an instance of its schema.

### `inst_checked`

`inst_checked(state, sigma, th)` is INST: it substitutes terms for free variables throughout a theorem, simultaneously.

```mbti
pub fn inst_checked(KernelState, Array[(Term, Term)], Thm) -> Result[Thm, LogicError]
```

$$
\frac{\Gamma \vdash p}{\Gamma\sigma \vdash p\sigma}\;\textsf{INST}
\qquad \sigma = [x_1 \mapsto t_1, \dots, x_n \mapsto t_n],\; x_i, t_i : \tau_i
$$

Unlike ABS, INST may touch variables that occur in the hypotheses, because it substitutes in the hypotheses too. Fails with `InvalidInstantiation` when a key is not a variable or occurs twice, and with `TypeMismatch` when a value has another type than its key.

```moonbit
test "primitive rules" {
  let st = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  // {p} |- p
  let th_p = @kernel.assume_checked(st, p).unwrap()
  inspect(@kernel.thm_to_string(th_p), content="[FVar(p : bool)] |- FVar(p : bool)")
  // {p = q} |- p = q, then EQ_MP gives {p = q, p} |- q
  let th_eq = @kernel.assume_checked(st, @kernel.mk_eq(p, q).unwrap()).unwrap()
  let th_q = @kernel.eq_mp_checked(st, th_eq, th_p).unwrap()
  inspect(@kernel.thm_hyp_count(th_q), content="2")
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_q).unwrap()), content="Var(q : bool)")
  // DEDUCT_ANTISYM on {p} |- p and {q} |- q gives {p, q} |- p = q
  let th_q0 = @kernel.assume_checked(st, q).unwrap()
  let th_pq = @kernel.deduct_antisym_rule_checked(st, th_p, th_q0).unwrap()
  inspect(@kernel.thm_hyp_count(th_pq), content="2")
  // INST renames p to q everywhere
  let th_inst = @kernel.inst_checked(st, [(p, q)], th_p).unwrap()
  inspect(@kernel.thm_to_string(th_inst), content="[FVar(q : bool)] |- FVar(q : bool)")
  // ASSUME needs a proposition
  let x = @kernel.mk_var("x", @kernel.mk_tyvar("A"))
  inspect(@kernel.assume_checked(st, x) is Err(@kernel.NotBoolTerm), content="true")
}
```

```moonbit
test "equality rules" {
  let st = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let x = @kernel.mk_var("x", a)
  let y = @kernel.mk_var("y", a)
  let id = @kernel.mk_abs(x, x)
  // BETA: |- (λx. x) y = y
  let th_beta = @kernel.beta_rule_checked(st, @kernel.mk_comb(id, y)).unwrap()
  let (_, rhs) = @kernel.dest_eq(@kernel.thm_concl(th_beta).unwrap()).unwrap()
  inspect(@kernel.term_to_string(rhs), content="Var(y : A)")
  // TRANS with REFL on the right-hand side changes nothing
  let th_t = @kernel.trans_checked(st, th_beta, @kernel.refl_checked(st, y).unwrap()).unwrap()
  inspect(@kernel.thm_to_string(th_t) == @kernel.thm_to_string(th_beta), content="true")
  // ABS over y is refused: y is free in the hypothesis {x = y}
  let th_h = @kernel.assume_checked(st, @kernel.mk_eq(x, y).unwrap()).unwrap()
  inspect(@kernel.abs_rule_checked(st, y, th_h) is Err(@kernel.VarFreeInHyp), content="true")
  // INST_TYPE: instantiate A := bool
  let th_b = @kernel.inst_type(st, [("A", @kernel.bool_ty())], th_beta).unwrap()
  assert_eq(@kernel.term_tyvars(@kernel.thm_concl(th_b).unwrap()), [])
  // BETA needs a redex
  inspect(@kernel.beta_rule_checked(st, y) is Err(@kernel.NotTrivialBetaRedex), content="true")
}
```

## Kernel state

### `KernelState`

`KernelState` is the abstract logical state: the scoped constant signature together with the theory history (definitions, type definitions, specifications, the infinity anchor and the audit certificates).

```mbti
type KernelState
```

States are immutable values. Every operation that extends a state returns a new one and leaves the old one valid, so an earlier state can be kept as the base of a conservativity check.

### `empty_kernel_state`

`empty_kernel_state` returns the initial state.

```mbti
pub fn empty_kernel_state() -> KernelState
```

It declares one constant, the choice operator `@` with identity `0` and schema $(\alpha \to \mathit{bool}) \to \alpha$, and admits the types `bool`, `ind` and `fun`. The equality constant `=` is built in and needs no declaration; `=` and `@` are reserved names.

### `ks_add_const`

`ks_add_const(state, name, ty)` declares a constant with the schema `ty` in the innermost scope and gives it a fresh identity.

```mbti
pub fn ks_add_const(KernelState, String, HolType) -> Result[KernelState, SigError]
```

Declaring the same name with the same type again in the same scope returns the state unchanged. Fails with `ConstTypeConflict` when the name is declared in the innermost scope with another type, `ReservedSymbol` for `=` and `@`, `DefinitionAlreadyExists` for a defined constant, `TypeRepresentationAlreadyExists` or `TypeAbstractionAlreadyExists` for a name taken by a type definition, and `TypeMismatch` when `ty` mentions a type the state does not admit.

### `ks_lookup_const`, `ks_const_schema` and `ks_lookup_const_id`

`ks_lookup_const` and `ks_const_schema` both return the declared schema of the constant visible under a name; `ks_lookup_const_id` returns its identity. The innermost declaration wins.

```mbti
pub fn ks_lookup_const(KernelState, String) -> HolType?
pub fn ks_const_schema(KernelState, String) -> HolType?
pub fn ks_lookup_const_id(KernelState, String) -> Int?
```

### `ks_mk_const` and `ks_mk_const_instance`

`ks_mk_const` builds an occurrence of the visible constant at its schema type, with its identity recorded. `ks_mk_const_instance` builds an occurrence at an instance of the schema.

```mbti
pub fn ks_mk_const(KernelState, String) -> Result[Term, SigError]
pub fn ks_mk_const_instance(KernelState, String, HolType) -> Result[Term, SigError]
```

Both fail with `UnknownConst` when no constant has the name. `ks_mk_const_instance` fails with `InvalidConstInstance` when the type is not an instance of the schema and with `TypeMismatch` when the type is not admissible.

### `ks_push_scope` and `ks_pop_scope`

`ks_push_scope` opens a new innermost scope; `ks_pop_scope` drops it and every constant declared in it.

```mbti
pub fn ks_push_scope(KernelState) -> KernelState
pub fn ks_pop_scope(KernelState) -> Result[KernelState, SigError]
```

A constant declared in an inner scope shadows an outer one with the same name and gets a new identity. Popping only changes the signature: definitions, type definitions and certificates recorded inside the scope stay in the theory history, so their names stay taken. `ks_pop_scope` fails with `ScopeUnderflow` on the outermost scope.

### `ks_sig`

`ks_sig` returns the signature part of a state.

```mbti
pub fn ks_sig(KernelState) -> GlobalSig
```

### `ks_type_is_admissible` and `ks_type_subst_is_admissible`

`ks_type_is_admissible` holds when every type constructor in a type is built in or admitted by a type definition, with the right arity. `ks_type_subst_is_admissible` holds when every type in a substitution is admissible.

```mbti
pub fn ks_type_is_admissible(KernelState, HolType) -> Bool
pub fn ks_type_subst_is_admissible(KernelState, Array[(String, HolType)]) -> Bool
```

### `ks_term_in_language` and `ks_thm_is_sentence_in_language`

`ks_term_in_language` holds when every type in a term is admissible and every constant occurrence is a declared constant at an instance of its schema, with a matching identity when one is recorded. `ks_thm_is_sentence_in_language` holds when a theorem has no hypotheses and its conclusion is a closed proposition in the language of the state.

```mbti
pub fn ks_term_in_language(KernelState, Term) -> Bool
pub fn ks_thm_is_sentence_in_language(KernelState, Thm) -> Bool
```

```moonbit
test "scopes and constants" {
  let st0 = @kernel.empty_kernel_state()
  let a = @kernel.mk_tyvar("A")
  let st1 = @kernel.ks_add_const(st0, "c", a).unwrap()
  inspect(@kernel.term_to_string(@kernel.ks_mk_const(st1, "c").unwrap()), content="Const(c#1 : A)")
  let c_bool = @kernel.ks_mk_const_instance(st1, "c", @kernel.bool_ty()).unwrap()
  inspect(@kernel.term_to_string(c_bool), content="Const(c#1 : bool)")
  let th = @kernel.refl_checked(st1, @kernel.ks_mk_const(st1, "c").unwrap()).unwrap()
  // shadow c in an inner scope: the old theorem is no longer admissible there
  let st2 = @kernel.ks_add_const(@kernel.ks_push_scope(st1), "c", @kernel.bool_ty()).unwrap()
  assert_eq(@kernel.ks_lookup_const_id(st2, "c"), Some(2))
  inspect(@kernel.thm_is_admissible(st2, th), content="false")
  // pop the scope: the outer c is visible again and the theorem is usable
  let st3 = @kernel.ks_pop_scope(st2).unwrap()
  assert_eq(@kernel.ks_lookup_const_id(st3, "c"), Some(1))
  inspect(@kernel.thm_is_admissible(st3, th), content="true")
  inspect(@kernel.ks_pop_scope(st3) is Err(@kernel.ScopeUnderflow), content="true")
  inspect(@kernel.ks_add_const(st0, "@", a) is Err(@kernel.ReservedSymbol), content="true")
}
```

## Signatures

A `GlobalSig` is the scoped constant table on its own, without the theory history. These functions operate on it directly; they never produce a `Thm`.

### `GlobalSig` and `ConstId`

`GlobalSig` is a stack of scopes, innermost last; each scope lists name, identity and schema. `ConstId` is the integer identity of a declared constant.

```mbti
pub enum GlobalSig {
  Sig(Array[Array[(String, Int, HolType)]])
}

pub type ConstId = Int
```

### `empty_sig`, `sig_push_scope` and `sig_pop_scope_e`

`empty_sig` is a signature with one empty scope; it does not contain `@`, unlike the signature of `empty_kernel_state`. `sig_push_scope` and `sig_pop_scope_e` open and close scopes; popping the last scope fails with `ScopeUnderflow`.

```mbti
pub fn empty_sig() -> GlobalSig
pub fn sig_push_scope(GlobalSig) -> GlobalSig
pub fn sig_pop_scope_e(GlobalSig) -> Result[GlobalSig, SigError]
```

### `sig_has_const`, `sig_lookup_const` and `sig_lookup_const_id`

These functions look a name up from the innermost scope outwards.

```mbti
pub fn sig_has_const(GlobalSig, String) -> Bool
pub fn sig_lookup_const(GlobalSig, String) -> HolType?
pub fn sig_lookup_const_id(GlobalSig, String) -> Int?
```

### `sig_add_const_idempotent_e`

`sig_add_const_idempotent_e` declares a constant in the innermost scope, with the next free identity, or returns the signature unchanged when the same declaration is already there.

```mbti
pub fn sig_add_const_idempotent_e(GlobalSig, String, HolType) -> Result[GlobalSig, SigError]
```

Fails with `ReservedSymbol` for `=` and `@` and with `ConstTypeConflict` when the innermost scope declares the name with another type.

### `sig_mk_const_e` and `sig_mk_const_instance_e`

These functions build a constant occurrence from a signature, like `ks_mk_const` and `ks_mk_const_instance`, but without the type admissibility check of a kernel state.

```mbti
pub fn sig_mk_const_e(GlobalSig, String) -> Result[Term, SigError]
pub fn sig_mk_const_instance_e(GlobalSig, String, HolType) -> Result[Term, SigError]
```

### `sig_define_const_e`

`sig_define_const_e(sig, name, rhs)` declares `name` at the type of `rhs` and returns the defining equation $\mathit{name} = \mathit{rhs}$ as a term.

```mbti
pub fn sig_define_const_e(GlobalSig, String, Term) -> Result[(GlobalSig, Term), SigError]
```

The equation is only a term, not a theorem: this function has no logical authority. Use `ks_define_const_thm` to obtain a definition theorem. Fails with `InvalidConstRhs` when `rhs` is ill-typed.

## Extension gates

The theory grows only through three gates. Each one checks its side conditions, records the new names in the theory history and appends an audit certificate.

### `ks_define_const` and `ks_define_const_thm`

`ks_define_const(state, c, ty, rhs)` is the definition gate `DefOK`: it declares the constant `c : ty` and records the definition $c = \mathit{rhs}$. `ks_define_const_thm` does the same and returns the definition theorem $\vdash c = \mathit{rhs}$; `ks_define_const` returns the equation as a term.

```mbti
pub fn ks_define_const(KernelState, String, HolType, Term) -> Result[(KernelState, Term), SigError]
pub fn ks_define_const_thm(KernelState, String, HolType, Term) -> Result[(KernelState, Thm), SigError]
```

The side conditions are: `c` is not reserved and not already defined or used by a type definition (`ReservedSymbol`, `DefinitionAlreadyExists`, `TypeRepresentationAlreadyExists`, `TypeAbstractionAlreadyExists`); `rhs` is closed (`DefinitionNotClosed`); `rhs` does not mention `c`, directly or through earlier definitions (`DefinitionIsCyclic`); `ty` is admissible (`InvalidConstRhs`) and equals the type of `rhs` (`TypeMismatch`); every type variable of `rhs` occurs in `ty` (`GhostTypeVariable`); and every constant of `rhs` is declared at an instance of its schema (`InvalidConstRhs`). The [kernel design](../design/kernel.md) shows why each condition is needed for conservativity.

### `ks_definition_theorem` and `ks_has_def_head`

`ks_definition_theorem` returns the recorded definition theorem of a defined constant, or `Err(UnknownConst)`. `ks_has_def_head` tests whether a name has been defined.

```mbti
pub fn ks_definition_theorem(KernelState, String) -> Result[Thm, SigError]
pub fn ks_has_def_head(KernelState, String) -> Bool
```

### `ks_register_type_definition`

`ks_register_type_definition(state, tycon, params, rep, pred, witness)` is the type definition gate `TypeDefOK`: it admits a new type constructor `tycon` of arity `params.length()` in bijection with the subset of the representation type carved out by `pred`.

```mbti
pub fn ks_register_type_definition(KernelState, String, Array[String], String, Term, Thm) -> Result[KernelState, SigError]
```

`pred` must be a closed abstraction $\lambda (x{:}\rho).\,P$ with $P : \mathit{bool}$ whose type variables are among `params`, and `witness` must be a hypothesis-free theorem $\vdash P[w/x]$ for a closed term `w`, which shows the subset is not empty. On success the state declares `rep : tycon(params) -> ρ` and `Abs_<tycon> : ρ -> tycon(params)` and records the contract theorems returned by `ks_typedef_contract`. Failures name the violated condition: `InvalidTypeParams`, `InvalidTypeArity`, `InvalidTypeRepName`, `InvalidTypeAbsName`, `TypeConstructorAlreadyExists`, `TypeRepresentationAlreadyExists`, `TypeAbstractionAlreadyExists`, `InvalidTypePredicate`, `TypeWitnessArityMismatch`, `InvalidTypeWitness`, `TypeWitnessPredicateMismatch`, `InvalidTypeDefinitionProduct`.

### `ks_typedef_contract` and `ks_has_typedef_contract`

`ks_typedef_contract(state, tycon)` returns the three contract theorems of a type definition, or `Err(MissingTypeDefinitionContract)`. `ks_has_typedef_contract` tests whether there is one.

```mbti
pub fn ks_typedef_contract(KernelState, String) -> Result[(Thm, Thm, Thm), SigError]
pub fn ks_has_typedef_contract(KernelState, String) -> Bool
```

With $\mathit{abs} = \texttt{Abs\_}\mathit{tycon}$ the three theorems are, in order:

$$
\vdash \mathit{abs}(\mathit{rep}\,a) = a
\qquad
\vdash P[\mathit{rep}\,a / x]
\qquad
P[r/x] \vdash \mathit{rep}(\mathit{abs}\,r) = r
$$

### `ks_has_type_witness`, `ks_has_type_rep_head` and `ks_has_type_abs_head`

`ks_has_type_witness(state, tycon, arity)` tests whether a type constructor of that arity is admitted; `ind` is admitted from the start. The other two test whether a name is the representation or abstraction function of a type definition.

```mbti
pub fn ks_has_type_witness(KernelState, String, Int) -> Bool
pub fn ks_has_type_rep_head(KernelState, String) -> Bool
pub fn ks_has_type_abs_head(KernelState, String) -> Bool
```

### `ks_specify_const`

`ks_specify_const(state, c, ty, pred, witness)` is the specification gate `SpecOK`: given $\vdash P[w/x]$ it introduces a constant `c : ty` and returns $\vdash P[c/x]$.

```mbti
pub fn ks_specify_const(KernelState, String, HolType, Term, Thm) -> Result[(KernelState, Thm), SigError]
```

The gate is derived from the choice operator and `DefOK`: it defines $c = (@\,\mathit{pred})$ through `ks_define_const_thm`, so the state records a `DefOK` certificate followed by a `SpecOK` certificate. The returned theorem is built by the gate; it is justified by the choice axiom, which the kernel does not expose as a theorem (see the [kernel design](../design/kernel.md)). The specification states the premise as $\vdash \exists x.\,P\,x$; the gate asks for a concrete witness instead. `pred` must be a closed abstraction over `ty` with no type variables outside `ty` (`InvalidSpecificationPredicate`, `SpecificationTypeVarLeak`), and `witness` must be a hypothesis-free theorem of the predicate at a closed term (`InvalidSpecificationWitness`). The definition conditions of `ks_define_const` apply to `c`.

### `ks_register_ind_infinity_axiom`, `ks_ind_infinity_axiom` and `ks_has_ind_infinity_axiom`

`ks_register_ind_infinity_axiom(state, anchor)` records a theorem about `ind` as the infinity anchor of the theory. `ks_ind_infinity_axiom` returns it, or `Err(MissingInfinityAnchor)`; `ks_has_ind_infinity_axiom` tests whether one is recorded.

```mbti
pub fn ks_register_ind_infinity_axiom(KernelState, Thm) -> Result[KernelState, SigError]
pub fn ks_ind_infinity_axiom(KernelState) -> Result[Thm, SigError]
pub fn ks_has_ind_infinity_axiom(KernelState) -> Bool
```

The anchor must already be a `Thm`: a hypothesis-free, admissible proposition that mentions `ind`. Registration therefore adds no new theorem; it only marks which theorem plays the role of the infinity assumption. It fails with `InvalidInfinityAnchor` when an anchor is already recorded or the theorem does not qualify.

```moonbit
test "definitions" {
  let st = @kernel.empty_kernel_state()
  let bool = @kernel.bool_ty()
  let x = @kernel.mk_var("x", bool)
  let bb = @kernel.fun_ty(bool, bool)
  let (st1, def_th) = @kernel.ks_define_const_thm(st, "idb", bb, @kernel.mk_abs(x, x)).unwrap()
  inspect(
    @kernel.thm_to_string(def_th),
    content="[] |- Comb(Comb(Const(= : fun(fun(bool, bool), fun(fun(bool, bool), bool))), Const(idb#1 : fun(bool, bool))), Abs(bool. BVar(0 : bool)))",
  )
  inspect(@kernel.ks_has_def_head(st1, "idb"), content="true")
  // a name can be defined only once, and a definition must be closed
  inspect(
    @kernel.ks_define_const(st1, "idb", bb, @kernel.mk_abs(x, x)) is Err(@kernel.DefinitionAlreadyExists),
    content="true",
  )
  inspect(@kernel.ks_define_const(st, "k", bool, x) is Err(@kernel.DefinitionNotClosed), content="true")
  // λy. y = λy. y mentions the type variable B, which the type bool does not
  let y = @kernel.mk_var("y", @kernel.mk_tyvar("B"))
  let ghost = @kernel.mk_eq(@kernel.mk_abs(y, y), @kernel.mk_abs(y, y)).unwrap()
  inspect(@kernel.ks_define_const(st, "g", bool, ghost) is Err(@kernel.GhostTypeVariable), content="true")
}
```

```moonbit
test "specification" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.ks_add_const(@kernel.empty_kernel_state(), "t0", bool).unwrap()
  let t0 = @kernel.ks_mk_const(st0, "t0").unwrap()
  let x = @kernel.mk_var("x", bool)
  let pred = @kernel.mk_abs(x, @kernel.mk_eq(x, t0).unwrap()) // λx. x = t0
  let witness = @kernel.refl_checked(st0, t0).unwrap() // |- t0 = t0
  let (st1, th) = @kernel.ks_specify_const(st0, "c", bool, pred, witness).unwrap()
  inspect(
    @kernel.thm_to_string(th),
    content="[] |- Comb(Comb(Const(= : fun(bool, fun(bool, bool))), Const(c#2 : bool)), Const(t0#1 : bool))",
  )
  inspect(@kernel.ks_extension_cert_count(st1), content="2")
}
```

```moonbit
test "type definition" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.ks_add_const(@kernel.empty_kernel_state(), "t0", bool).unwrap()
  let b = @kernel.mk_var("b", bool)
  let pred = @kernel.mk_abs(b, @kernel.mk_eq(b, b).unwrap()) // every bool
  let t0 = @kernel.ks_mk_const(st0, "t0").unwrap()
  let witness = @kernel.refl_checked(st0, t0).unwrap() // |- t0 = t0
  let st1 = @kernel.ks_register_type_definition(st0, "copy", [], "rep_copy", pred, witness).unwrap()
  inspect(@kernel.ks_type_is_admissible(st1, @kernel.mk_tyapp("copy", [])), content="true")
  assert_eq(
    @kernel.ks_lookup_const(st1, "Abs_copy").map(@kernel.hol_type_to_string),
    Some("fun(bool, copy)"),
  )
  let (abs_rep, _, _) = @kernel.ks_typedef_contract(st1, "copy").unwrap()
  inspect(
    @kernel.term_to_string(@kernel.thm_concl(abs_rep).unwrap()),
    content="Comb(Comb(Const(= : fun(copy, fun(copy, bool))), Comb(Const(Abs_copy : fun(bool, copy)), Comb(Const(rep_copy : fun(copy, bool)), Var(a : copy)))), Var(a : copy))",
  )
}
```

## Audit and replay

### `ExtensionGate` and `ExtensionCert`

`ExtensionGate` names the gate that admitted an extension. An `ExtensionCert` is the audit record of one admission: the gate, the names it introduced and a digest of the witness or definition theorem.

```mbti
pub enum ExtensionGate {
  DefOK
  TypeDefOK
  SpecOK
}

pub type ExtensionCert = (ExtensionGate, Array[String], String)
```

### `ks_extension_cert_count` and `ks_extension_cert_at`

These functions read the certificates of a state in admission order.

```mbti
pub fn ks_extension_cert_count(KernelState) -> Int
pub fn ks_extension_cert_at(KernelState, Int) -> (ExtensionGate, Array[String], String)?
```

Certificates record what happened; they are not proof objects and cannot be turned into theorems.

### `ks_conservative_replay_ok`

`ks_conservative_replay_ok(base, extended, th)` is the executable conservativity check: it holds when `th` is admissible in `extended`, is a closed hypothesis-free sentence in the language of `base`, and is admissible in `base`. It checks the side conditions of the conservativity theorem, not a derivation: it does not rebuild a proof of `th` in `base`. When it holds and `extended` was reached from `base` through the gates, the conservativity theorem of the specification says that `th` is also a theorem of `base`.

```mbti
pub fn ks_conservative_replay_ok(KernelState, KernelState, Thm) -> Bool
```

Regression tests use it to check that a theorem proved after an extension is stated in the old language, so that the conservativity theorem applies to it.

```moonbit
test "audit" {
  let bool = @kernel.bool_ty()
  let st0 = @kernel.empty_kernel_state()
  let x = @kernel.mk_var("x", bool)
  let id = @kernel.mk_abs(x, x)
  let (st1, _) = @kernel.ks_define_const_thm(st0, "idb", @kernel.fun_ty(bool, bool), id).unwrap()
  inspect(@kernel.ks_extension_cert_count(st1), content="1")
  let (gate, heads, _) = @kernel.ks_extension_cert_at(st1, 0).unwrap()
  inspect(gate is @kernel.DefOK && heads == ["idb"], content="true")
  // |- (λx. x) = (λx. x) does not mention idb: it replays in the base theory
  let th = @kernel.refl_checked(st1, id).unwrap()
  inspect(@kernel.ks_conservative_replay_ok(st0, st1, th), content="true")
}
```

## Errors

### `LogicError`

`LogicError` is raised as a value by term constructors and primitive rules.

```mbti
pub suberror LogicError {
  TypeMismatch
  VariableCaptured
  NotAnEquality
  NotBoolTerm
  AlphaMismatch
  InvalidInstantiation
  VarFreeInHyp
  NotTrivialBetaRedex
  BoundaryFailure
  CapacityExceeded
}
```

| Constructor | Meaning |
| --- | --- |
| `TypeMismatch` | A term is ill-typed, types that must agree differ, or a constant is unknown to the state. |
| `VariableCaptured` | A substitution value is a loose bound index. Values built from named terms never are. |
| `NotAnEquality` | A premise or term that must be an equation is not one. |
| `NotBoolTerm` | A term that must be a proposition has another type. |
| `AlphaMismatch` | Terms that must be α-equivalent are not. |
| `InvalidInstantiation` | A substitution is malformed, an ABS binder is not a variable, or a theorem does not fit the constant identities of the state. |
| `VarFreeInHyp` | The ABS variable occurs free in a hypothesis. |
| `NotTrivialBetaRedex` | BETA was given a term that is not a β-redex. |
| `BoundaryFailure` | A term could not be converted between named and De Bruijn form. |
| `CapacityExceeded` | A De Bruijn index computation would overflow. |

### `SigError`

`SigError` is raised as a value by signature operations and extension gates.

```mbti
pub suberror SigError {
  DuplicateConstName
  ConstTypeConflict
  InvalidConstInstance
  UnknownConst
  ScopeUnderflow
  InvalidConstRhs
  ReservedSymbol
  DefinitionAlreadyExists
  DefinitionNotClosed
  DefinitionIsCyclic
  GhostTypeVariable
  InvalidTypeWitness
  InvalidTypePredicate
  InvalidTypeRepName
  InvalidTypeAbsName
  InvalidTypeParams
  InvalidTypeArity
  TypeWitnessArityMismatch
  TypeWitnessPredicateMismatch
  TypeConstructorAlreadyExists
  TypeRepresentationAlreadyExists
  TypeAbstractionAlreadyExists
  InvalidInfinityAnchor
  MissingInfinityAnchor
  InvalidTypeDefinitionProduct
  MissingTypeDefinitionContract
  InvalidSpecificationWitness
  InvalidSpecificationPredicate
  SpecificationTypeVarLeak
  TypeMismatch
}
```

| Group | Constructors |
| --- | --- |
| Signature | `DuplicateConstName`, `ConstTypeConflict`, `InvalidConstInstance`, `UnknownConst`, `ScopeUnderflow`, `ReservedSymbol`, `TypeMismatch` |
| `DefOK` | `InvalidConstRhs`, `DefinitionAlreadyExists`, `DefinitionNotClosed`, `DefinitionIsCyclic`, `GhostTypeVariable` |
| `TypeDefOK` | `InvalidTypeWitness`, `InvalidTypePredicate`, `InvalidTypeRepName`, `InvalidTypeAbsName`, `InvalidTypeParams`, `InvalidTypeArity`, `TypeWitnessArityMismatch`, `TypeWitnessPredicateMismatch`, `TypeConstructorAlreadyExists`, `TypeRepresentationAlreadyExists`, `TypeAbstractionAlreadyExists`, `InvalidTypeDefinitionProduct`, `MissingTypeDefinitionContract` |
| `SpecOK` | `InvalidSpecificationWitness`, `InvalidSpecificationPredicate`, `SpecificationTypeVarLeak` |
| Infinity anchor | `InvalidInfinityAnchor`, `MissingInfinityAnchor` |

Both error types are values: match them with `is` or in a `match`, as the examples on this page do.
