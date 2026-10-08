# logic design

The `logic` package turns the equality calculus of the kernel into propositional logic. It defines the connectives as kernel definitions, derives the natural-deduction rules from the ten primitive rules, and keeps the catalog of theorem names that proof scripts may cite. This page gives the definitions, derives the rules, and explains why the package can do all this without being trusted.

## Design goal

The kernel knows only equality and choice. Users want $\top$, $\bot$, $\wedge$, $\Rightarrow$, $\neg$ and $\vee$ with their usual rules. The goal is to provide them with no new authority: every connective is a definition admitted by the `DefOK` gate, and every rule is a MoonBit function that calls kernel rules. The package may be wrong in the sense of failing to prove something, but it cannot prove anything false.

## Mathematical background

### Connectives as definitions

QED follows the definitions of HOL Light, where every connective is reduced to equality.[^hol-defs] Let $t$ be the truth term $(\lambda x.\,x) = (\lambda x.\,x)$. The prelude defines

$$
\begin{aligned}
\top &:= t \\
\bot &:= (\lambda p.\,p) = (\lambda p.\,t) \\
\mathit{and} &:= \lambda p\,q.\;(\lambda f.\,f\,p\,q) = (\lambda f.\,f\,t\,t) \\
\mathit{imp} &:= \lambda p\,q.\;\mathit{and}'\,p\,q = p \\
\mathit{not} &:= \lambda p.\;\mathit{imp}'\,p\,\bot' \\
\mathit{or} &:= \lambda p\,q.\;\mathit{imp}'\,(\mathit{not}'\,p)\,q
\end{aligned}
$$

[^hol-defs]: J. Harrison, *HOL Light Tutorial*, section on the logical constants; the definitions go back to Andrews' type theory Q0. QED's disjunction differs from HOL Light's, see below.

where a primed name stands for the definition body already expanded, so that each right-hand side is a closed term over $=$ alone. The reading of each definition:

- $t$ is true because it is an instance of REFL.
- $\bot$ says the identity predicate on booleans equals the constantly-true predicate, that is $\forall p.\,p$ with $\forall P := (P = \lambda x.\,t)$. It is false in the standard model because $\bot$ itself would have to be true.
- $p \wedge q$ says the pair $(p, q)$ cannot be told apart from $(t, t)$ by any function $f$, which holds exactly when $p$ and $q$ are both true.
- $p \Rightarrow q$ is $(p \wedge q) = p$: adding $q$ to $p$ changes nothing.
- $\neg p$ is $p \Rightarrow \bot$.
- $p \vee q$ is $\neg p \Rightarrow q$.

### Basis terms

`prop_mk_and` and its siblings return the *basis* form, the expanded right-hand side, rather than the application $\mathit{and}\,p\,q$ of the constant. The rules below work on basis forms, because only on those can the kernel rules act directly; the constants exist so that the definitions are recorded, can be cited, and can be recognised in terms that users write.

## Design decisions

### Derive, do not postulate

Every rule of the package is a derivation. The derivations below are the ones the code performs; each line is a kernel rule.

**Truth.** From the definition $\vdash \top = t$, symmetry gives $\vdash t = \top$, and $\vdash t$ is REFL, so EQ_MP gives $\vdash \top$ (`logic_prop_truth_const_thm`). Symmetry itself is derived:

$$
\begin{aligned}
&\vdash (=) = (=) && \textsf{REFL} \\
&\Gamma \vdash (=)\,s = (=)\,t && \textsf{MK\_COMB}(\cdot,\ \Gamma \vdash s = t) \\
&\Gamma \vdash (s = s) = (t = s) && \textsf{MK\_COMB}(\cdot,\ \vdash s = s) \\
&\Gamma \vdash t = s && \textsf{EQ\_MP}(\cdot,\ \vdash s = s)
\end{aligned}
$$

**From a proof to an equation with truth.** From $\Gamma \vdash p$ and $\vdash t$, DEDUCT_ANTISYM_RULE gives $\Gamma \setminus \{t\} \vdash p = t$, and $\Gamma \setminus \{t\} = \Gamma$ unless $t$ is itself a hypothesis, in which case dropping it is harmless because $t$ is provable. This "EQT_INTRO" step is how propositions are put inside terms.

**Conjunction introduction.** From $\Gamma \vdash p$ and $\Delta \vdash q$ obtain $\Gamma \vdash p = t$ and $\Delta \vdash q = t$. For a fresh variable $f$,

$$
\begin{aligned}
&\vdash f = f && \textsf{REFL} \\
&\Gamma \vdash f\,p = f\,t && \textsf{MK\_COMB} \\
&\Gamma \cup \Delta \vdash f\,p\,q = f\,t\,t && \textsf{MK\_COMB} \\
&\Gamma \cup \Delta \vdash (\lambda f.\,f\,p\,q) = (\lambda f.\,f\,t\,t) && \textsf{ABS},\ f \notin \mathrm{FV}(\Gamma \cup \Delta)
\end{aligned}
$$

The last line is $p \wedge q$. Freshness of $f$ is what makes ABS applicable.

**Conjunction elimination.** Apply both sides of $\Gamma \vdash (\lambda f.\,f\,p\,q) = (\lambda f.\,f\,t\,t)$ to the selector $\lambda x\,y.\,x$ with MK_COMB and REFL, then reduce both sides with BETA and TRANS:

$$
\Gamma \vdash (\lambda x\,y.\,x)\,p\,q = (\lambda x\,y.\,x)\,t\,t
\quad\leadsto\quad
\Gamma \vdash p = t
$$

Symmetry and EQ_MP with $\vdash t$ give $\Gamma \vdash p$. The selector $\lambda x\,y.\,y$ gives $q$.

**Implication elimination.** From $\Gamma \vdash (p \wedge q) = p$ and $\Delta \vdash p$: symmetry gives $\Gamma \vdash p = (p \wedge q)$, EQ_MP gives $\Gamma \cup \Delta \vdash p \wedge q$, and conjunction elimination gives $q$.

**Implication introduction.** From $\Gamma \vdash q$ with $p \in \Gamma$: conjunction introduction with $\{p\} \vdash p$ gives $\Gamma \vdash p \wedge q$, and elimination from the assumption gives $\{p \wedge q\} \vdash p$. Then

$$
\frac{\Gamma \vdash p \wedge q \qquad \{p \wedge q\} \vdash p}{(\Gamma \setminus \{p\}) \cup (\{p \wedge q\} \setminus \{p \wedge q\}) \vdash (p \wedge q) = p}\;\textsf{DEDUCT\_ANTISYM\_RULE}
$$

and the hypothesis set is $\Gamma \setminus \{p\}$. The conclusion is $p \Rightarrow q$ by definition. `logic_prop_imp_intro_thm` requires $p \in \Gamma$; discharging an absent hypothesis would need weakening first.

**Ex falso.** From $\Gamma \vdash (\lambda p.\,p) = (\lambda p.\,t)$ and any proposition $q$, MK_COMB with $\vdash q = q$ and two BETA steps give $\Gamma \vdash q = t$, hence $\Gamma \vdash q$. Negation elimination is implication elimination with conclusion $\bot$.

**Disjunction introduction.** From $\Gamma \vdash p$: assume $\neg p$, eliminate it against $p$ to get $\bot$, derive $q$ by ex falso, and discharge $\neg p$:

$$
\Gamma \vdash \neg p \Rightarrow q \;=\; p \vee q.
$$

From $\Delta \vdash q$ the right introduction discharges an unused $\neg p$ after conjoining it with $q$.

### No disjunction elimination

The prelude defines $p \vee q$ as $\neg p \Rightarrow q$. Introduction is derivable, as shown. Elimination, from $p \vee q$, $p \Rightarrow r$ and $q \Rightarrow r$ infer $r$, is not: it needs a case split on $p$, that is excluded middle $p \vee \neg p$. In HOL excluded middle follows from the choice axiom and extensionality (Diaconescu's theorem),[^diaconescu] but the kernel exposes no theorem for the choice axiom and the package does not derive excluded middle. Rather than ship a rule it cannot justify, the catalog has `or_intro_l` and `or_intro_r` and no `or_elim`, and the tactic layer has `left` and `right` but no case analysis.

[^diaconescu]: R. Diaconescu, "Axiom of choice and complementation", Proc. AMS 51, 1975. HOL Light derives `EXCLUDED_MIDDLE` this way in `class.ml`.

### Trusted recognition of connective constants

**Problem.** A user can declare a constant named `and` that means something else. If `prop_dest_and` recognised any application of a constant called `and`, a tactic could treat an arbitrary term as a conjunction.

**Choice.** The destructors accept the basis form, which is checked structurally, and an application of a connective constant only when the state holds the canonical definition theorem for that constant (with the current identity). `install_prop_prelude` refuses to install over a placeholder constant with the right name and type but no definition.

**Why.** Recognition errors would not break soundness, because every rule is replayed through the kernel. They would produce confusing failures at replay time instead of clear failures at the tactic, and the specification requires connector recognition to be backed by definitions.

### One catalog, two modes

**Problem.** `exact th` and `apply th` mean different things. `exact` needs a theorem whose conclusion is the goal; `apply` needs an implication whose consequent is the goal and leaves its antecedent as the new goal. Letting a name be used in the wrong mode silently would either fail late or, worse, make `exact` quietly behave like `apply`.

**Choice.** Each catalog entry records an `exact_class` and an `apply_class`. `exact` consults only the first, `apply` only the second, and a name that exists but is unusable in a mode resolves to `KnownButUnavailable`, which the tactics layer reports as a shape or apply mismatch. A local hypothesis name always takes precedence over a catalog name and never falls back to it.

**Why.** The table is the single source for the tactics layer, the prover's corpus, the mapping matrix and the documentation, so the theorem names a user may write cannot drift between them.

### Errors from the kernel only

Kernel error constructors are read-only outside the kernel. The package obtains the `LogicError` and `SigError` values it returns by running small kernel operations that are known to fail in the required way. This keeps the error vocabulary owned by the kernel, at the cost of less specific errors: many helper failures surface as `TypeMismatch` or `AlphaMismatch`.

## Correctness and invariants

- **Soundness.** Every `Thm` returned by this package is the result of kernel functions, so the kernel's soundness argument covers it. The derivations above show that each rule is also *complete* for its intended use: whenever its premises have the stated shapes, it succeeds.
- **Conservativity of the prelude.** The six constants are admitted by `DefOK` with closed right-hand sides, no type variables and no cycles, so the prelude is a conservative extension of the empty theory.
- **Idempotence.** `install_prop_prelude(install_prop_prelude(s))` equals `install_prop_prelude(s)`: an existing canonical definition is accepted as is.
- **Exact sequents.** The replay helpers check hypotheses as sets up to α-equivalence. `logic_prop_strengthen_to_hyps` only adds hypotheses, so a theorem that needs a hypothesis the goal does not have is rejected rather than accepted with extra assumptions.
- **β-normalisation is proof-producing.** `logic_beta_normalize_eq` and `logic_normalize_prop_beta` build kernel equations step by step; the term-level `logic_beta_nf_*` functions return the right-hand side of such an equation. Normalisation does not enter abstractions and is bounded (512 steps per pass, 32 passes for the deep form), which suffices for the connective encodings.

## Alternatives rejected

- **Connectives as kernel primitives.** This would add rules to the kernel and to its soundness proof. Definitions cost nothing in trust.
- **HOL Light's disjunction** $\forall r.\,(p \Rightarrow r) \Rightarrow (q \Rightarrow r) \Rightarrow r$. With it, elimination is derivable without excluded middle, at the cost of a universal quantifier over propositions inside every disjunction. The prelude uses the shorter encoding and states its limit instead; switching would change every disjunction term and the corpus built on them.
- **A mixed resolver.** `logic_prop_resolve_ref` resolves names without distinguishing modes; it is kept for tests, while the tactics layer uses the mode-specific resolvers.

## Boundaries

- The package proves propositional facts only; it has no quantifier rules beyond what the tactics layer builds for theorem-header binders.
- It has no disjunction elimination, no excluded middle and no classical reasoning.
- It does not store user theorems: the catalog is fixed in the source, and adding a name means adding code and a test.
- It adds no authority. Any change to it is reviewed for usefulness, not for soundness.
- It does not parse or print formulas; terms are built by the [parser](parser.md) and printed by the kernel's structural printer.
