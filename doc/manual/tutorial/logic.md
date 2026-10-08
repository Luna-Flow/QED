# logic tutorial

This tutorial uses the `logic` package to prove propositional theorems forwards: you install the connectives, build formulas, and combine natural-deduction rules into proofs such as commutativity of conjunction. Every step returns a kernel theorem, so what you build here is exactly what the tactics layer builds behind a proof script.

| I want to | Use |
| --- | --- |
| Install the connectives `T`, `F`, `and`, `imp`, `not`, `or` | `install_prop_prelude`, `default_prop_prelude` |
| Build and take apart formulas | `prop_mk_and`, `prop_mk_imp`, `prop_mk_not`, `prop_mk_or`, `prop_dest_and`, `prop_dest_or` |
| Introduce or eliminate a conjunction | `logic_prop_and_intro_thm`, `logic_prop_and_elim_l_thm`, `logic_prop_and_elim_r_thm` |
| Discharge a hypothesis or use an implication | `logic_prop_imp_intro_thm`, `logic_prop_imp_elim_thm` |
| Reason with negation and falsity | `logic_prop_not_elim`, `logic_prop_ex_falso_thm` |
| Prove a disjunction | `logic_prop_or_intro_l_thm`, `logic_prop_or_intro_r_thm` |
| List the theorem names scripts may cite | `logic_prop_theorem_count`, `logic_prop_theorem_at` |
| Reduce the β-redexes left by unfolding | `logic_normalize_prop_beta` |

## Quick start

Import the kernel and the logic package in `moon.pkg`:

```text
import {
  "Luna-Flow/QED/kernel",
  "Luna-Flow/QED/logic",
}
```

Install the propositional prelude into a kernel state, then prove $\vdash \top$:

```moonbit
test "quick start" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let th = @logic.logic_prop_truth_const_thm(st, pre).unwrap()
  inspect(@kernel.thm_to_string(th), content="[] |- Const(T#1 : bool)")
}
```

The `#1` is the identity of the constant `T`, the first constant the prelude declares. `install_prop_prelude` defines `T`, `F`, `and`, `imp`, `not` and `or` through the kernel's definition gate. `default_prop_prelude()` is the record of those names that every function of the package takes.

## Everyday tasks

### Build formulas

Connective builders take propositions and return terms. They check that their arguments are of type `bool`.

```moonbit
test "formulas" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let q = @kernel.mk_var("q", @kernel.bool_ty())
  let p_and_q = @logic.prop_mk_and(st, pre, p, q).unwrap()
  let p_or_q = @logic.prop_mk_or(st, pre, p, q).unwrap()
  // the destructors recover the parts
  let (l, r) = @logic.prop_dest_and(st, pre, p_and_q).unwrap()
  inspect(@kernel.term_to_string(l) + ", " + @kernel.term_to_string(r), content="Var(p : bool), Var(q : bool)")
  inspect(@logic.prop_dest_or(st, pre, p_or_q) is Some(_), content="true")
  // a disjunction is not a conjunction
  inspect(@logic.prop_dest_and(st, pre, p_or_q) is None, content="true")
}
```

The terms are large, because each connective is its definition expanded down to equality; compare them with `term_alpha_eq` and take them apart with the `prop_dest_*` functions rather than printing them.

### Prove commutativity of conjunction

Assume $p \wedge q$, take it apart, put it back together the other way round, and discharge the assumption:

```moonbit
test "and commutes" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let q = @kernel.mk_var("q", @kernel.bool_ty())
  let p_and_q = @logic.prop_mk_and(st, pre, p, q).unwrap()
  let h = @logic.logic_assume(st, p_and_q).unwrap() // {p ∧ q} |- p ∧ q
  let th_p = @logic.logic_prop_and_elim_l_thm(st, pre, h).unwrap() // {p ∧ q} |- p
  let th_q = @logic.logic_prop_and_elim_r_thm(st, pre, h).unwrap() // {p ∧ q} |- q
  let th_qp = @logic.logic_prop_and_intro_thm(st, pre, th_q, th_p).unwrap() // {p ∧ q} |- q ∧ p
  let th = @logic.logic_prop_imp_intro_thm(st, pre, p_and_q, th_qp).unwrap() // |- p ∧ q -> q ∧ p
  inspect(@kernel.thm_hyp_count(th), content="0")
  let goal = @logic.prop_mk_imp(st, pre, p_and_q, @logic.prop_mk_and(st, pre, q, p).unwrap()).unwrap()
  inspect(@kernel.term_alpha_eq(@kernel.thm_concl(th).unwrap(), goal), content="true")
}
```

This is the theorem that the script `and_comm` in the [prover tutorial](prover.md) proves; the tactic layer performs the same calls.

### Chain implications

Modus ponens is `logic_prop_imp_elim_thm`. From $p \Rightarrow q$ and $q \Rightarrow r$ and $p$, derive $r$:

```moonbit
test "chain" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let r = @kernel.mk_var("r", bool)
  let pq = @logic.logic_assume(st, @logic.prop_mk_imp(st, pre, p, q).unwrap()).unwrap()
  let qr = @logic.logic_assume(st, @logic.prop_mk_imp(st, pre, q, r).unwrap()).unwrap()
  let th_p = @logic.logic_assume(st, p).unwrap()
  let th_q = @logic.logic_prop_imp_elim_thm(st, pre, pq, th_p).unwrap()
  let th_r = @logic.logic_prop_imp_elim_thm(st, pre, qr, th_q).unwrap()
  inspect(@kernel.term_to_string(@kernel.thm_concl(th_r).unwrap()), content="Var(r : bool)")
  inspect(@kernel.thm_hyp_count(th_r), content="3")
  // modus ponens needs the antecedent, not some other fact
  inspect(@logic.logic_prop_imp_elim_thm(st, pre, qr, th_p) is Err(_), content="true")
}
```

### Use negation and falsity

$\neg p$ is $p \Rightarrow \bot$, so a proof of $p$ and a proof of $\neg p$ give $\bot$, and from $\bot$ anything follows:

```moonbit
test "contradiction" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let goal = @kernel.mk_var("anything", bool)
  let th_p = @logic.logic_assume(st, p).unwrap()
  let th_np = @logic.logic_assume(st, @logic.prop_mk_not(st, pre, p).unwrap()).unwrap()
  let th_f = @logic.logic_prop_not_elim(st, pre, th_np, th_p).unwrap()
  let th = @logic.logic_prop_ex_falso_thm(st, pre, th_f, goal).unwrap()
  inspect(@kernel.term_to_string(@kernel.thm_concl(th).unwrap()), content="Var(anything : bool)")
}
```

### Look up catalog names

Proof scripts cite theorems by name. The catalog says which names exist and in which mode they work:

```moonbit
test "catalog" {
  let names = []
  for i in 0..<@logic.logic_prop_theorem_count() {
    let e = @logic.logic_prop_theorem_at(i).unwrap()
    if e.apply_class is Some(_) {
      names.push(e.name)
    }
  }
  // the names `apply` accepts
  inspect(names.join(" "), content="and_elim_l and_elim_r or_intro_l or_intro_r eq_sym")
}
```

## Going further

**Fit a theorem to a goal.** Backward proof needs theorems whose hypotheses are exactly those of a goal. `logic_prop_ensure_sequent(state, hyps, concl, th)` checks the conclusion and weakens `th` to exactly `hyps`, and fails if `th` depends on something the goal does not provide. The [tactics](tactics.md) layer calls it every time it closes a goal.

**Normalise.** Unfolding a connective constant leaves a β-redex. `logic_normalize_prop_beta` reduces it with kernel steps:

```moonbit
test "unfold and normalise" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let p = @kernel.mk_var("p", @kernel.bool_ty())
  let not_c = @kernel.ks_mk_const(st, "not").unwrap()
  let th = @logic.logic_assume(st, @kernel.mk_comb(not_c, p)).unwrap() // {not p} |- not p
  let unfolded = @logic.logic_prop_unfold_not(st, pre, th).unwrap() // {not p} |- ¬p
  let concl = @kernel.thm_concl(unfolded).unwrap()
  inspect(@kernel.term_alpha_eq(concl, @logic.prop_mk_not(st, pre, p).unwrap()), content="true")
}
```

**Extend the theory.** The extension wrappers (`logic_specify_const`, `logic_register_typedef`) are the kernel gates under names that belong to this layer; upper layers call them so they need not import the kernel's gate functions directly.

**Mind the missing rule.** There is no disjunction elimination; the [logic design](../design/logic.md) explains why. Prove a disjunction with `logic_prop_or_intro_l_thm` or `logic_prop_or_intro_r_thm`, and avoid designs that need case analysis on one.

## Common pitfalls

- **Forgetting the prelude.** Builders work on any state, but `logic_prop_truth_const_thm`, the `logic_prop_def_*` functions and recognition of connective constants need `install_prop_prelude` first.
- **Squatting a connective name.** A state that already declares `and` without its canonical definition cannot take the prelude; `install_prop_prelude` refuses it.
- **Discharging a hypothesis that is not there.** `logic_prop_imp_intro_thm(state, pre, p, th)` needs `p` among the hypotheses of `th`. Weaken first with `logic_add_assum` if you want a vacuous implication.
- **Expecting basis form after unfolding a binary connective.** `logic_prop_unfold_and`, `_imp` and `_or` leave $(\lambda p\,q.\,\dots)\,a\,b$ unreduced; call `logic_normalize_prop_beta`.
- **Reading error constructors literally.** Helper failures are reported with generic kernel errors such as `TypeMismatch`. Check the shape of your premises when a helper fails.

## Next steps

- The [logic API](../api/logic.md) lists every function, including the replay helpers.
- The [logic design](../design/logic.md) derives each rule from the kernel rules.
- The [tactics tutorial](tactics.md) uses these rules backwards, from goals.
