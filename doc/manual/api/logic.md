# logic API

## Purpose

The `logic` package (`Luna-Flow/QED/logic`) is the checked helper layer over the kernel. It defines the propositional connectives as kernel definitions, builds and recognises connective terms, derives the propositional rules from the primitive ones, and keeps the catalog of theorem names that `exact` and `apply` understand. It depends only on `kernel` and has no authority of its own: every theorem it returns was produced by kernel rules, so a bug here can make a proof fail but cannot make a false theorem.

All functions are pure. Theorem-producing functions return `Result[@kernel.Thm, @kernel.LogicError]`; helpers that may find nothing return an `Option`. The logic behind the definitions is explained in the [logic design](../design/logic.md) and a walk-through is in the [logic tutorial](../tutorial/logic.md).

In the formulas on this page, $\top$ is the constant `T`, $\bot$ the constant `F`, and $p \wedge q$, $p \Rightarrow q$, $\neg p$, $p \vee q$ the connective terms built by `prop_mk_and`, `prop_mk_imp`, `prop_mk_not` and `prop_mk_or`.

## Importing

Add the package to your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/QED/logic",
  "Luna-Flow/QED/kernel",
}
```

The examples on this page are blackbox tests. They refer to this package as `@logic` and also use `@kernel`, so they import both packages.

## Prelude

### `PropPrelude`

`PropPrelude` names the constants of the propositional prelude and lists its rule names.

```mbti
pub struct PropPrelude {
  truth_name : String
  false_name : String
  imp_name : String
  not_name : String
  and_name : String
  or_name : String
  rules : Array[PropRule]
}
```

Most functions of this package take a `PropPrelude` to know which constants to look for in the state.

### `PropRule`

`PropRule` is a named propositional rule with its number of premises.

```mbti
pub struct PropRule {
  name : String
  premise_count : Int
}
```

### `default_prop_prelude`

`default_prop_prelude` returns the prelude used everywhere in QED: the constants `T`, `F`, `imp`, `not`, `and`, `or`, and the rules `imp_intro`, `imp_elim`, `and_intro`, `and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`.

```mbti
pub fn default_prop_prelude() -> PropPrelude
```

### `install_prop_prelude`

`install_prop_prelude` defines the six prelude constants in a kernel state through the `DefOK` gate.

```mbti
pub fn install_prop_prelude(@kernel.KernelState) -> Result[@kernel.KernelState, @kernel.SigError]
```

It is idempotent: a constant that already has exactly the canonical definition is kept. A constant with the same name that is only declared, or defined differently, is refused with `DefinitionAlreadyExists`, and one with another type with `ConstTypeConflict`. On an empty state it adds six `DefOK` certificates.

### `prop_prelude_rule_count`, `prop_prelude_rule_at` and `prop_prelude_has_rule`

These functions read the rule list of a prelude.

```mbti
pub fn prop_prelude_rule_count(PropPrelude) -> Int
pub fn prop_prelude_rule_at(PropPrelude, Int) -> PropRule?
pub fn prop_prelude_has_rule(PropPrelude, String) -> Bool
```

### `prop_truth_name` and `prop_false_name`

These functions return the names of the truth and falsity constants.

```mbti
pub fn prop_truth_name(PropPrelude) -> String
pub fn prop_false_name(PropPrelude) -> String
```

```moonbit
test "prelude" {
  let pre = @logic.default_prop_prelude()
  inspect(@logic.prop_prelude_rule_count(pre), content="7")
  inspect(@logic.prop_prelude_has_rule(pre, "and_intro"), content="true")
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  inspect(@kernel.ks_extension_cert_count(st), content="6")
  // installing again changes nothing
  let st2 = @logic.install_prop_prelude(st).unwrap()
  inspect(@kernel.ks_extension_cert_count(st2), content="6")
  // a placeholder constant named `and` blocks the prelude
  let bool = @kernel.bool_ty()
  let and_ty = @kernel.fun_ty(bool, @kernel.fun_ty(bool, bool))
  let squatted = @kernel.ks_add_const(@kernel.empty_kernel_state(), "and", and_ty).unwrap()
  inspect(@logic.install_prop_prelude(squatted) is Err(_), content="true")
}
```

## Connective terms

### `prop_mk_and`, `prop_mk_imp`, `prop_mk_not` and `prop_mk_or`

These functions build the connective terms. They return the *basis* form, the right-hand side of the definition applied to the arguments, not an application of the constant.

```mbti
pub fn prop_mk_and(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn prop_mk_imp(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn prop_mk_not(@kernel.KernelState, PropPrelude, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn prop_mk_or(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
```

The forms are

$$
\begin{aligned}
p \wedge q &:= (\lambda f.\,f\,p\,q) = (\lambda f.\,f\,t\,t) \\
p \Rightarrow q &:= (p \wedge q) = p \\
\neg p &:= p \Rightarrow \bot_0 \\
p \vee q &:= \neg p \Rightarrow q
\end{aligned}
$$

where $t$ is the truth term $(\lambda x.\,x) = (\lambda x.\,x)$ and $\bot_0$ is the falsity term of `logic_prop_false_term`. They fail with `NotBoolTerm` when an argument is not a proposition and with `TypeMismatch` when it is ill-typed. They do not need the prelude to be installed.

> [!WARNING]
> The binder $f$ of the conjunction is a variable with the fixed name `_p_and` and type $\mathit{bool} \to \mathit{bool} \to \mathit{bool}$, and the builders do not rename it. If an argument contains a free variable with exactly that name and type, the builder captures it and the result is not $p \wedge q$; `logic_prop_and_intro_thm` and the rules built on it then fail. Do not use the name `_p_and` for your own variables.

### `prop_dest_and`, `prop_dest_imp`, `prop_dest_not` and `prop_dest_or`

These functions recognise connective terms and return their arguments, or `None`.

```mbti
pub fn prop_dest_and(@kernel.KernelState, PropPrelude, @kernel.Term) -> (@kernel.Term, @kernel.Term)?
pub fn prop_dest_imp(@kernel.KernelState, PropPrelude, @kernel.Term) -> (@kernel.Term, @kernel.Term)?
pub fn prop_dest_not(@kernel.KernelState, PropPrelude, @kernel.Term) -> @kernel.Term?
pub fn prop_dest_or(@kernel.KernelState, PropPrelude, @kernel.Term) -> (@kernel.Term, @kernel.Term)?
```

They accept the basis form, and also an application of the prelude constant when the state holds the canonical definition theorem for it. A constant with the right name but without that definition is not recognised, so a look-alike constant cannot pass as a connective.

### `logic_prop_truth_term` and `logic_prop_false_term`

These functions return the basis terms of truth and falsity: $(\lambda x.\,x) = (\lambda x.\,x)$ and $(\lambda p.\,p) = (\lambda p.\,t)$, the latter being $\forall p.\,p$ in HOL's encoding.

```mbti
pub fn logic_prop_truth_term() -> @kernel.Term
pub fn logic_prop_false_term() -> @kernel.Term
```

```moonbit
test "connectives" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let imp = @logic.prop_mk_imp(st, pre, p, q).unwrap()
  let (a, b) = @logic.prop_dest_imp(st, pre, imp).unwrap()
  inspect(@kernel.term_to_string(a) + " -> " + @kernel.term_to_string(b), content="Var(p : bool) -> Var(q : bool)")
  // p -> q is the equation (p ∧ q) = p
  let (lhs, _) = @kernel.dest_eq(imp).unwrap()
  inspect(@kernel.term_alpha_eq(lhs, @logic.prop_mk_and(st, pre, p, q).unwrap()), content="true")
  // connectives only take propositions
  let x = @kernel.mk_var("x", @kernel.mk_tyvar("A"))
  inspect(@logic.prop_mk_and(st, pre, p, x) is Err(@kernel.NotBoolTerm), content="true")
}
```

## Definition theorems

### `logic_prop_def_imp`, `logic_prop_def_not`, `logic_prop_def_and` and `logic_prop_def_or`

These functions return the definition theorem of a connective constant from the state, for example $\vdash \mathit{and} = \lambda p\,q.\,p \wedge q$.

```mbti
pub fn logic_prop_def_imp(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.SigError]
pub fn logic_prop_def_not(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.SigError]
pub fn logic_prop_def_and(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.SigError]
pub fn logic_prop_def_or(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.SigError]
```

They fail with `UnknownConst` when the prelude is not installed.

### `logic_bool_false_def_thm`

`logic_bool_false_def_thm` returns the definition theorem of `F`.

```mbti
pub fn logic_bool_false_def_thm(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.SigError]
```

### `logic_prop_def_lhs` and `logic_prop_def_rhs`

These functions return the two sides of an equational theorem, typically a definition.

```mbti
pub fn logic_prop_def_lhs(@kernel.Thm) -> Result[@kernel.Term, @kernel.LogicError]
pub fn logic_prop_def_rhs(@kernel.Thm) -> Result[@kernel.Term, @kernel.LogicError]
```

### `logic_prop_unfold_head`

`logic_prop_unfold_head(state, th_def, th)` replaces the head constant of the conclusion of `th` by its definition: from $\vdash c = \lambda \bar x.\,b$ and $\Gamma \vdash c\,\bar a$ it derives $\Gamma \vdash (\lambda \bar x.\,b)\,\bar a$, with head β-redexes contracted by `logic_beta_normalize_eq`.

```mbti
pub fn logic_prop_unfold_head(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

The head must be the defined constant, applied to at most two arguments; otherwise the function fails with `AlphaMismatch` or `TypeMismatch`. Only a redex at the very head is contracted. With one argument, $(\lambda x.\,b)\,a$ is such a redex and the result is $b[a/x]$; with two arguments the head is $((\lambda x\,y.\,b)\,a_1)\,a_2$, whose function part is not an abstraction, so the conclusion stays unreduced. Apply `logic_normalize_prop_beta` to reach the basis form.

### `logic_prop_unfold_imp`, `logic_prop_unfold_not`, `logic_prop_unfold_and` and `logic_prop_unfold_or`

These functions are `logic_prop_unfold_head` with the definition of one connective constant. `logic_prop_unfold_not` turns $\Gamma \vdash \mathit{not}\,p$ into $\Gamma \vdash \neg p$ in basis form; the two-argument forms return the unreduced application described above.

```mbti
pub fn logic_prop_unfold_imp(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_unfold_not(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_unfold_and(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_unfold_or(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

```moonbit
test "unfold" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  // {and p q} |- and p q, with `and` the prelude constant
  let and_c = @kernel.ks_mk_const(st, "and").unwrap()
  let and_pq = @kernel.mk_comb(@kernel.mk_comb(and_c, p), q)
  let th = @logic.logic_assume(st, and_pq).unwrap()
  let unfolded = @logic.logic_prop_unfold_and(st, pre, th).unwrap()
  // the definition is substituted, but (λp q. ...) p q is not yet reduced
  let basis = @logic.prop_mk_and(st, pre, p, q).unwrap()
  inspect(@kernel.term_alpha_eq(@kernel.thm_concl(unfolded).unwrap(), basis), content="false")
  let reduced = @logic.logic_normalize_prop_beta(st, unfolded).unwrap()
  inspect(@kernel.term_alpha_eq(@kernel.thm_concl(reduced).unwrap(), basis), content="true")
}
```

## Kernel rule wrappers

These functions call the corresponding kernel rule unchanged. They exist so that upper layers depend on `logic` rather than reaching into the kernel for every step.

### `logic_refl`, `logic_assume`, `logic_add_assum` and `logic_trans`

```mbti
pub fn logic_refl(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_assume(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_add_assum(@kernel.KernelState, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_trans(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

They are `refl_checked`, `assume_checked`, `add_assum_checked` and `trans_checked`.

### `logic_mk_comb_rule`, `logic_abs_rule` and `logic_beta_rule`

```mbti
pub fn logic_mk_comb_rule(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_abs_rule(@kernel.KernelState, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_beta_rule(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

They are `mk_comb_rule_checked`, `abs_rule_checked` and `beta_rule_checked`.

### `logic_eq_mp` and `logic_deduct_antisym`

```mbti
pub fn logic_eq_mp(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_deduct_antisym(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

They are `eq_mp_checked` and `deduct_antisym_rule_checked`.

### `logic_inst_type` and `logic_inst`

```mbti
pub fn logic_inst_type(@kernel.KernelState, Array[(String, @kernel.HolType)], @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_inst(@kernel.KernelState, Array[(@kernel.Term, @kernel.Term)], @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

They are `inst_type` and `inst_checked`.

## Extension wrappers

These functions call the kernel extension gates and audit readers unchanged.

### `logic_register_typedef` and `logic_typedef_contract`

```mbti
pub fn logic_register_typedef(@kernel.KernelState, String, Array[String], String, @kernel.Term, @kernel.Thm) -> Result[@kernel.KernelState, @kernel.SigError]
pub fn logic_typedef_contract(@kernel.KernelState, String) -> Result[(@kernel.Thm, @kernel.Thm, @kernel.Thm), @kernel.SigError]
```

They are `ks_register_type_definition` (`TypeDefOK`) and `ks_typedef_contract`.

### `logic_specify_const`

```mbti
pub fn logic_specify_const(@kernel.KernelState, String, @kernel.HolType, @kernel.Term, @kernel.Thm) -> Result[(@kernel.KernelState, @kernel.Thm), @kernel.SigError]
```

It is `ks_specify_const` (`SpecOK`).

### `logic_register_ind_infinity_anchor` and `logic_ind_infinity_anchor`

```mbti
pub fn logic_register_ind_infinity_anchor(@kernel.KernelState, @kernel.Thm) -> Result[@kernel.KernelState, @kernel.SigError]
pub fn logic_ind_infinity_anchor(@kernel.KernelState) -> Result[@kernel.Thm, @kernel.SigError]
```

They are `ks_register_ind_infinity_axiom` and `ks_ind_infinity_axiom`.

### `logic_extension_cert_count`, `logic_extension_cert_at` and `logic_conservative_replay_ok`

```mbti
pub fn logic_extension_cert_count(@kernel.KernelState) -> Int
pub fn logic_extension_cert_at(@kernel.KernelState, Int) -> (@kernel.ExtensionGate, Array[String], String)?
pub fn logic_conservative_replay_ok(@kernel.KernelState, @kernel.KernelState, @kernel.Thm) -> Bool
```

They are `ks_extension_cert_count`, `ks_extension_cert_at` and `ks_conservative_replay_ok`.

## Equality tools

### `logic_eq_sym`

`logic_eq_sym` derives symmetry of equality: from $\Gamma \vdash s = t$ it proves $\Gamma \vdash t = s$.

```mbti
pub fn logic_eq_sym(@kernel.KernelState, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

The derivation uses REFL, MK_COMB twice and EQ_MP; the [kernel tutorial](../tutorial/kernel.md) builds the same rule step by step. Fails with `NotAnEquality` when the premise is not an equation.

### `logic_eq_mp_bool`

`logic_eq_mp_bool` is EQ_MP with an explicit check that the second premise is a proposition.

```mbti
pub fn logic_eq_mp_bool(@kernel.KernelState, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_apply_fun_eq` and `logic_apply_fun_eq2`

These functions apply both sides of a function equation to arguments: from $\Gamma \vdash f = g$ they prove $\Gamma \vdash f\,a = g\,a$, or $\Gamma \vdash f\,a\,b = g\,a\,b$.

```mbti
pub fn logic_apply_fun_eq(@kernel.KernelState, @kernel.Thm, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_apply_fun_eq2(@kernel.KernelState, @kernel.Thm, @kernel.Term, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_beta_normalize_eq` and `logic_normalize_prop_beta`

`logic_beta_normalize_eq` contracts head β-redexes of the right-hand side of an equation for as long as the right-hand side is one: from $\Gamma \vdash s = t$ it proves $\Gamma \vdash s = t'$. `logic_normalize_prop_beta` reduces the conclusion of a theorem more thoroughly: it repeatedly contracts the leftmost-outermost redex found along application spines (not under abstractions), up to 512 steps, and from $\Gamma \vdash c$ proves $\Gamma \vdash c'$.

```mbti
pub fn logic_beta_normalize_eq(@kernel.KernelState, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_normalize_prop_beta(@kernel.KernelState, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

Both chain kernel steps (BETA and TRANS, plus REFL and MK_COMB to reach redexes inside applications), so the result is a kernel theorem, not a rewritten term. After 512 steps `logic_normalize_prop_beta` returns what it has reached, which may still contain redexes.

### `logic_beta_nf_bool_term` and `logic_beta_nf_bool_term_deep`

These functions compute the β-normal form of a proposition by proving $\vdash t = t'$ and returning $t'$. The deep form repeats until a fixed point, within a bound.

```mbti
pub fn logic_beta_nf_bool_term(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
pub fn logic_beta_nf_bool_term_deep(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Term, @kernel.LogicError]
```

The tactics layer uses them to compare a finished theorem with its goal up to β-equivalence.

## Propositional theorems

These functions derive the natural-deduction rules of propositional logic from the kernel rules and the connective definitions.

### `logic_prop_truth_thm` and `logic_prop_truth_const_thm`

`logic_prop_truth_thm` proves the truth term, $\vdash (\lambda x.\,x) = (\lambda x.\,x)$, by REFL. `logic_prop_truth_const_thm` proves $\vdash \top$ for the constant `T`, using its definition.

```mbti
pub fn logic_prop_truth_thm(@kernel.KernelState) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_truth_const_thm(@kernel.KernelState, PropPrelude) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_and_intro_thm`, `logic_prop_and_elim_l_thm` and `logic_prop_and_elim_r_thm`

These functions are conjunction introduction and elimination.

```mbti
pub fn logic_prop_and_intro_thm(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_and_elim_l_thm(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_and_elim_r_thm(@kernel.KernelState, PropPrelude, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

$$
\frac{\Gamma \vdash p \quad \Delta \vdash q}{\Gamma \cup \Delta \vdash p \wedge q}
\qquad
\frac{\Gamma \vdash p \wedge q}{\Gamma \vdash p}
\qquad
\frac{\Gamma \vdash p \wedge q}{\Gamma \vdash q}
$$

### `logic_prop_imp_intro_thm`, `logic_prop_imp_elim_thm` and `logic_prop_imp_refl`

`logic_prop_imp_intro_thm(state, pre, p, th)` discharges the hypothesis `p`; `logic_prop_imp_elim_thm` is modus ponens; `logic_prop_imp_refl` proves $\vdash p \Rightarrow p$.

```mbti
pub fn logic_prop_imp_intro_thm(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_imp_elim_thm(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_imp_refl(@kernel.KernelState, PropPrelude, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

$$
\frac{\Gamma \vdash q \quad p \in \Gamma}{\Gamma \setminus \{p\} \vdash p \Rightarrow q}
\qquad
\frac{\Gamma \vdash p \Rightarrow q \quad \Delta \vdash p}{\Gamma \cup \Delta \vdash q}
\qquad
\frac{}{\vdash p \Rightarrow p}
$$

`logic_prop_imp_intro_thm` fails when `p` is not a hypothesis of `th`. `logic_prop_imp_elim_thm` fails when the second theorem does not prove the antecedent.

### `logic_prop_not_elim` and `logic_prop_ex_falso_thm`

`logic_prop_not_elim` derives falsity from a proposition and its negation; `logic_prop_ex_falso_thm(state, pre, th_false, q)` derives any proposition `q` from falsity.

```mbti
pub fn logic_prop_not_elim(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_ex_falso_thm(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

$$
\frac{\Gamma \vdash \neg p \quad \Delta \vdash p}{\Gamma \cup \Delta \vdash \bot_0}
\qquad
\frac{\Gamma \vdash \bot_0 \quad q : \mathit{bool}}{\Gamma \vdash q}
$$

### `logic_prop_or_intro_l_thm` and `logic_prop_or_intro_r_thm`

These functions are disjunction introduction: `logic_prop_or_intro_l_thm(state, pre, th_p, q)` proves $p \vee q$ from $p$, and `logic_prop_or_intro_r_thm(state, pre, p, th_q)` proves $p \vee q$ from $q$.

```mbti
pub fn logic_prop_or_intro_l_thm(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_or_intro_r_thm(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

There is no disjunction elimination: with $p \vee q := \neg p \Rightarrow q$ it would need excluded middle, which the prelude does not derive. The [logic design](../design/logic.md) explains this.

```moonbit
test "natural deduction" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let th_p = @logic.logic_assume(st, p).unwrap()
  let th_q = @logic.logic_assume(st, q).unwrap()
  // {p, q} |- p ∧ q, then {p, q} |- q
  let th_pq = @logic.logic_prop_and_intro_thm(st, pre, th_p, th_q).unwrap()
  let th_r = @logic.logic_prop_and_elim_r_thm(st, pre, th_pq).unwrap()
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_r).unwrap()), content="Var(q : bool)")
  // discharge p: {q} |- p -> p ∧ q
  let th_imp = @logic.logic_prop_imp_intro_thm(st, pre, p, th_pq).unwrap()
  inspect(@kernel.thm_hyp_count(th_imp), content="1")
  // modus ponens gives back {p, q} |- p ∧ q
  let th_mp = @logic.logic_prop_imp_elim_thm(st, pre, th_imp, th_p).unwrap()
  inspect(@kernel.thm_hyp_count(th_mp), content="2")
  // |- p -> p
  let th_refl = @logic.logic_prop_imp_refl(st, pre, p).unwrap()
  inspect(@kernel.thm_hyp_count(th_refl), content="0")
  // |- T, for the prelude constant T
  let th_t = @logic.logic_prop_truth_const_thm(st, pre).unwrap()
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_t).unwrap()), content="Const(T#1 : bool)")
}
```

```moonbit
test "negation and disjunction" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let th_p = @logic.logic_assume(st, p).unwrap()
  let th_not_p = @logic.logic_assume(st, @logic.prop_mk_not(st, pre, p).unwrap()).unwrap()
  // {¬p, p} |- ⊥, and from ⊥ anything follows
  let th_false = @logic.logic_prop_not_elim(st, pre, th_not_p, th_p).unwrap()
  let th_q = @logic.logic_prop_ex_falso_thm(st, pre, th_false, q).unwrap()
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_q).unwrap()), content="Var(q : bool)")
  // {p} |- p ∨ q
  let th_or = @logic.logic_prop_or_intro_l_thm(st, pre, th_p, q).unwrap()
  inspect(
    @kernel.term_alpha_eq(@kernel.thm_concl(th_or).unwrap(), @logic.prop_mk_or(st, pre, p, q).unwrap()),
    content="true",
  )
}
```

## Replay helpers

The tactics layer closes goals by replaying kernel steps. These helpers make a theorem fit a goal sequent exactly.

### `logic_prop_assume`

`logic_prop_assume` is `logic_assume` under the name the replay code uses.

```mbti
pub fn logic_prop_assume(@kernel.KernelState, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_strengthen_to_hyps`

`logic_prop_strengthen_to_hyps(state, hyps, th)` adds the missing hypotheses of `hyps` to `th` by weakening, and checks that the result has exactly the hypotheses `hyps`.

```mbti
pub fn logic_prop_strengthen_to_hyps(@kernel.KernelState, Array[@kernel.Term], @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

It fails when `th` has a hypothesis outside `hyps`: weakening can add hypotheses but never remove them.

### `logic_prop_close_hypothesis` and `logic_prop_ensure_sequent`

`logic_prop_close_hypothesis(state, hyps, c)` proves the sequent $\mathit{hyps} \vdash c$ when `c` is one of `hyps`. `logic_prop_ensure_sequent(state, hyps, c, th)` checks that `th` concludes `c` and returns it with exactly the hypotheses `hyps`.

```mbti
pub fn logic_prop_close_hypothesis(@kernel.KernelState, Array[@kernel.Term], @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_ensure_sequent(@kernel.KernelState, Array[@kernel.Term], @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_discharge_imp_prefix`

`logic_prop_discharge_imp_prefix(state, pre, [a1, ..., an], th)` discharges the hypotheses $a_n, \dots, a_1$ in turn, turning $\Gamma \vdash q$ into $\Gamma \setminus \{a_1, \dots, a_n\} \vdash a_1 \Rightarrow \dots \Rightarrow a_n \Rightarrow q$.

```mbti
pub fn logic_prop_discharge_imp_prefix(@kernel.KernelState, PropPrelude, Array[@kernel.Term], @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_replay_imp_elim_backward` and `logic_prop_replay_imp_elim_backward_thm`

These functions finish a backward `apply` step. Given the goal hypotheses, an implication $a \Rightarrow b$ (as a hypothesis term, or as a theorem) and a proof of $a$, they prove $b$ under exactly the goal hypotheses.

```mbti
pub fn logic_prop_replay_imp_elim_backward(@kernel.KernelState, PropPrelude, Array[@kernel.Term], @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_replay_imp_elim_backward_thm(@kernel.KernelState, PropPrelude, Array[@kernel.Term], @kernel.Thm, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_replay_and_elim_l` and `logic_prop_replay_and_elim_r`

These functions eliminate a conjunction and check that the result is the expected term.

```mbti
pub fn logic_prop_replay_and_elim_l(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_replay_and_elim_r(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_merge_conjunction`

`logic_prop_merge_conjunction(state, pre, th_a, th_b, and_term)` introduces a conjunction and checks that it is `and_term`; `split` uses it to join its two branches.

```mbti
pub fn logic_prop_merge_conjunction(@kernel.KernelState, PropPrelude, @kernel.Thm, @kernel.Thm, @kernel.Term) -> Result[@kernel.Thm, @kernel.LogicError]
```

### `logic_prop_or_wrap_left` and `logic_prop_or_wrap_right`

These functions introduce a disjunction from its left or right branch and check, up to β-normal form, that it is the expected disjunction; `left` and `right` use them.

```mbti
pub fn logic_prop_or_wrap_left(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
pub fn logic_prop_or_wrap_right(@kernel.KernelState, PropPrelude, @kernel.Term, @kernel.Term, @kernel.Thm) -> Result[@kernel.Thm, @kernel.LogicError]
```

The arguments are the full disjunction, the other branch and the proof of the chosen branch.

```moonbit
test "replay helpers" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  // close the goal  p, q |- p  from the hypothesis p
  let th = @logic.logic_prop_close_hypothesis(st, [p, q], p).unwrap()
  inspect(@kernel.thm_hyp_count(th), content="2")
  // a theorem with an extra hypothesis cannot be fitted to a smaller sequent
  let th_pq = @logic.logic_prop_and_intro_thm(
    st,
    pre,
    @logic.logic_assume(st, p).unwrap(),
    @logic.logic_assume(st, q).unwrap(),
  ).unwrap()
  inspect(@logic.logic_prop_strengthen_to_hyps(st, [p], th_pq) is Err(_), content="true")
}
```

## Theorem catalog

The catalog is the single list of theorem names that proof scripts may use with `exact` and `apply`.

### `PropTheoremClass` and `PropTheoremEntry`

`PropTheoremEntry` describes a catalog name: its number of premises and how `exact` and `apply` may use it. `PropTheoremClass` says how a name closes a goal.

```mbti
pub enum PropTheoremClass {
  DirectClose
  ImplicationBacked
  ContextDerived
}

pub struct PropTheoremEntry {
  name : String
  premise_count : Int
  exact_class : PropTheoremClass?
  apply_class : PropTheoremClass?
}
```

`DirectClose` closes a goal outright (`truth`, `imp_refl`, `eq_refl`). `ContextDerived` closes a goal using facts found among the hypotheses and locals (`and_elim_l` from a conjunction in context). `ImplicationBacked` turns a goal into the premise of an implication (`apply or_intro_l`). A `None` class means the name is not available in that mode.

| Name | Premises | `exact` | `apply` |
| --- | --- | --- | --- |
| `imp_refl` | 0 | `DirectClose` | none |
| `truth` | 0 | `DirectClose` | none |
| `and_elim_l` | 1 | `ContextDerived` | `ImplicationBacked` |
| `and_elim_r` | 1 | `ContextDerived` | `ImplicationBacked` |
| `and_intro` | 2 | `ContextDerived` | none |
| `not_elim` | 2 | `ContextDerived` | none |
| `ex_falso` | 1 | `ContextDerived` | none |
| `or_intro_l` | 1 | none | `ImplicationBacked` |
| `or_intro_r` | 1 | none | `ImplicationBacked` |
| `imp_elim` | 2 | `ContextDerived` | none |
| `eq_refl` | 0 | `DirectClose` | none |
| `eq_sym` | 1 | `ContextDerived` | `ImplicationBacked` |
| `eq_mp` | 2 | `ContextDerived` | none |

### `logic_prop_theorem_count`, `logic_prop_theorem_at` and `logic_prop_theorem_entry`

These functions read the catalog, by index or by name.

```mbti
pub fn logic_prop_theorem_count() -> Int
pub fn logic_prop_theorem_at(Int) -> PropTheoremEntry?
pub fn logic_prop_theorem_entry(String) -> PropTheoremEntry?
```

### `logic_prop_named_theorem`

`logic_prop_named_theorem(state, pre, name, goal)` builds the theorem of a `DirectClose` name for the given goal conclusion, or returns `None` when the name does not close that goal.

```mbti
pub fn logic_prop_named_theorem(@kernel.KernelState, PropPrelude, String, @kernel.Term) -> @kernel.Thm?
```

### `logic_prop_context_theorem` and `logic_prop_context_apply_theorem`

`logic_prop_context_theorem(state, pre, name, pool, goal)` builds the theorem of a `ContextDerived` name from the facts in `pool`, together with the fact it used. `logic_prop_context_apply_theorem` builds the implication theorem of an `ImplicationBacked` name together with the antecedent that becomes the new goal.

```mbti
pub fn logic_prop_context_theorem(@kernel.KernelState, PropPrelude, String, Array[@kernel.Term], @kernel.Term) -> (@kernel.Thm, @kernel.Term)?
pub fn logic_prop_context_apply_theorem(@kernel.KernelState, PropPrelude, String, Array[@kernel.Term], @kernel.Term) -> (@kernel.Thm, @kernel.Term)?
```

### `PropExactWitness`, `PropExactWitnessResolution`, `PropExactTheoremResolution`, `PropApplyTheoremResolution` and `PropRefResolution`

The resolvers below return one of these types. `KnownButUnavailable` and its variants mean that the name is in the catalog but does not apply to this goal in this mode; the tactics layer reports that as a goal-shape or apply mismatch rather than as an unknown name.

```mbti
pub enum PropApplyTheoremResolution {
  Applicable(@kernel.Thm, @kernel.Term)
  KnownButUnavailable
}

pub enum PropExactTheoremResolution {
  ExactApplicable(@kernel.Thm)
  ExactKnownButUnavailable
}

pub enum PropExactWitness {
  ExactLocalAlias(String)
  ExactDirectTheorem(String, @kernel.Thm)
  ExactContextTheorem(String, @kernel.Thm, Array[@kernel.Term])
}

pub enum PropExactWitnessResolution {
  ExactWitnessApplicable(PropExactWitness)
  ExactWitnessKnownButUnavailable
}

pub enum PropRefResolution {
  LocalFact(@kernel.Term)
  NamedTheorem(@kernel.Thm)
  ContextDerived(@kernel.Thm, @kernel.Term)
}
```

### `logic_prop_resolve_exact_witness`

`logic_prop_resolve_exact_witness(state, pre, locals, hyps, goal, name)` resolves the argument of `exact`. A local name is looked up first and, once found, never falls back to a catalog name: it is applicable only when it is an active hypothesis equal to the goal. Otherwise the catalog is consulted in `exact` mode. Returns `None` for a name that is neither local nor in the catalog.

```mbti
pub fn logic_prop_resolve_exact_witness(@kernel.KernelState, PropPrelude, Array[(String, @kernel.Term)], Array[@kernel.Term], @kernel.Term, String) -> PropExactWitnessResolution?
```

### `logic_prop_resolve_exact_theorem` and `logic_prop_resolve_apply_theorem`

These functions resolve a catalog name in `exact` or `apply` mode against a pool of facts, without looking at locals. `None` means the name is not in the catalog.

```mbti
pub fn logic_prop_resolve_exact_theorem(@kernel.KernelState, PropPrelude, Array[@kernel.Term], @kernel.Term, String) -> PropExactTheoremResolution?
pub fn logic_prop_resolve_apply_theorem(@kernel.KernelState, PropPrelude, Array[@kernel.Term], @kernel.Term, String) -> PropApplyTheoremResolution?
```

### `logic_prop_resolve_ref`

`logic_prop_resolve_ref` is the older resolver that mixes modes; it is kept for tests and non-tactic callers. `ProofState` and `prover` use the mode-specific resolvers.

```mbti
pub fn logic_prop_resolve_ref(@kernel.KernelState, PropPrelude, Array[(String, @kernel.Term)], Array[@kernel.Term], @kernel.Term, String) -> PropRefResolution?
```

```moonbit
test "catalog" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  inspect(@logic.logic_prop_theorem_count(), content="13")
  let e = @logic.logic_prop_theorem_entry("or_intro_l").unwrap()
  inspect(e.exact_class is None && e.apply_class is Some(@logic.ImplicationBacked), content="true")
  let t = @kernel.ks_mk_const(st, "T").unwrap()
  // `exact truth` closes the goal T
  let r = @logic.logic_prop_resolve_exact_theorem(st, pre, [], t, "truth")
  inspect(r is Some(@logic.ExactApplicable(_)), content="true")
  // `apply truth` is known but not usable: truth is not an implication
  let r2 = @logic.logic_prop_resolve_apply_theorem(st, pre, [], t, "truth")
  inspect(r2 is Some(@logic.KnownButUnavailable), content="true")
  // an unknown name resolves to nothing
  inspect(@logic.logic_prop_resolve_apply_theorem(st, pre, [], t, "nope") is None, content="true")
}
```
