#set page(paper: "a4", margin: (x: 2.4cm, y: 2.2cm))
#set par(justify: true, leading: 0.62em)
#set text(size: 10.5pt)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#let info-color = rgb("#1d4ed8")
#let warning-color = rgb("#ca8a04")
#let critical-color = rgb("#b91c1c")

#let level-color(level) = {
  if level == "info" {
    info-color
  } else if level == "warning" {
    warning-color
  } else {
    critical-color
  }
}

#let keyblock(level, title, body) = {
  let color = level-color(level)
  rect(
    inset: 10pt,
    radius: 5pt,
    stroke: 0.5pt + color,
    fill: color.lighten(86%),
    [
      #text(fill: color)[#title]
      #v(0.35em)
      #body
    ],
  )
}

#align(center)[
  #text(size: 16pt, weight: "bold")[A Formal Mathematical Specification for QED]
  #linebreak()
  #text(size: 11pt)[A Minimal LCF-Style HOL Kernel in MoonBit]
]

#v(1.2em)

= Abstract

QED is an interactive theorem prover in MoonBit, designed around an LCF-style trusted kernel and a higher-order logic foundation. This document gives a formal, implementation-aware specification of its core theory. The presentation starts from first principles: signatures, type formation, term formation, typing judgments, substitution laws, theorem objects, and primitive inference rules. The objective is to make the trust model and proof discipline explicit enough that a reader can understand the logic of the system without reading source code.

#v(0.8em)
#keyblock("info", [Reading Guide], [
  The document is intentionally ordered from basic theory to derived engineering consequences. A reader should be able to stop after the foundational sections and still obtain a coherent understanding of the QED kernel.
])

#set heading(numbering: "1.")

= Notation and Meta-Level Conventions

This section fixes the notation baseline used by all later definitions and rules.

- Object-language judgments are written with $tack.r$, e.g. $Gamma tack.r t : tau$.
- Partial computation/evaluation at the meta level is written with $mapsto$, e.g. $f(x) mapsto y$.
- Named-term alpha-equivalence is written $equiv_alpha$.
- De Bruijn structural equivalence is written $tilde.equiv$.
- Semantic interpretation (denotation) is written with double brackets, e.g. $⟦t⟧_rho$ for term meaning under environment $rho$.

Layering discipline:

1. *Object layer*: syntax, typing, theorem sequents, and primitive rules.
2. *Boundary layer*: named/De Bruijn conversion partial functions.
3. *Meta layer*: proofs about invariants, commutation, and soundness.

All claims below explicitly indicate which layer they inhabit.

Per-section dependency template (used throughout this manuscript):

- *Defines*: new syntax/judgments introduced in the section.
- *Depends on*: earlier sections required for well-formedness.
- *Used by*: later rules/theorems that rely on this section.

= Motivation and Design Goal

The central engineering goal of QED is to separate trusted reasoning from untrusted proof search. In an LCF architecture, theorem creation is restricted to a very small set of primitive kernel operations. Everything else, including automation and tactics, is merely a theorem-producing program that calls those primitives.

This architecture has two consequences:

1. Correctness is reduced to the soundness of a small kernel.
2. Rich user tooling can evolve without expanding the trusted code base.

The mathematical role of this document is to state the object language and inference rules precisely enough to support both consequences.

= Positioning and Related Systems

QED is positioned as a minimal, auditable HOL kernel rather than a full proof-assistant platform. The design goal is to keep the trusted core small, make boundary assumptions explicit, and allow tactic/automation layers to evolve independently.

*Definition (Design Target).*
QED prioritizes kernel verifiability over feature breadth: every exported theorem object must be traceable to primitive kernel rules under explicit side conditions.

Compared with mainstream systems:

- HOL Light: same LCF trust model and primitive-rule discipline, but QED currently executes primitive cores on De Bruijn objects and then lifts to named boundaries.
- Coq: richer dependent type theory and broader automation ecosystem, while QED currently focuses on STT/HOL kernel minimality.
- Isabelle: mature logical framework and extensive libraries, while QED intentionally optimizes for a compact, implementation-aligned kernel specification.

= Foundational Theory

== Signatures and Symbols

Let $Sigma_t$ be a type-constructor signature. Each constructor $k in Sigma_t$ has a natural-number arity $a(k) in NN$.

Let $Sigma_c$ be a term-constant signature. Each constant $c in Sigma_c$ is assigned a simple type.

In the current QED kernel, $Sigma_c$ is managed by a scoped signature stack:

- each scope stores a finite partial map from constant names to types;
- lookup proceeds from the innermost scope to the outermost scope;
- same-name insertion is rejected inside one scope but allowed in a nested scope (shadowing).

For polymorphic constants, the assigned type is read as a principal type schema (universally quantified at the meta level), and concrete uses are type instances of that schema.

QED reserves two distinguished type constructors:

- $"bool"$ with arity $0$.
- $"fun"$ with arity $2$.

These are sufficient to define simply typed lambda terms with boolean propositions.

For next-stage conservative theory construction, QED additionally fixes one trusted
foundation type constructor:

- $"ind"$ with arity $0$.

`"ind"` is the carrier used by the explicit infinity-anchor assumption; it is not
introduced by user-level extension rules.

== Constant Type Schemes and Instance Relation

To avoid polymorphism lockout while preserving kernel typing discipline, constant typing uses a principal-schema + instance relation.

*Definition (Constant Principal Type).*
Each resolved constant identity carries a principal simple type schema:
$
  kappa_c : tau_"gen"
$
where type variables in $tau_"gen"$ are implicitly universally quantified.

*Definition (Type Instance Relation).*
For types $tau$ and $tau_"gen"$, write
$
  tau ≼ tau_"gen"
$
iff there exists a type substitution $theta$ such that
$
  tau = theta(tau_"gen")
$
and $theta$ maps only type variables.

This relation is used by elaboration and core typing of `RConst`, including user constants and reserved logical constants.

== Logical Constants and Reserved Symbols

The kernel distinguishes *logical symbols* from ordinary signature-managed constants.

*Definition (Reserved Equality Symbol).*
The symbol $"="$ is a reserved polymorphic logical constant with schematic type
$
  "=" : Π alpha. "fun"(alpha, "fun"(alpha, "bool"))
$
and is not inserted by user signature operations.

*Definition (Reserved Choice Operator).*
The symbol $"@"$ is a reserved polymorphic choice operator with schematic type
$
  "@" : Π alpha. "fun"("fun"(alpha, "bool"), alpha)
$
and is not inserted by user signature operations.

*Axiom Schema (Choice).*
For each type instance $alpha$ and predicate $P : "fun"(alpha, "bool")$:
$
  tack.r (exists x : alpha. P(x)) => P("@"(P))
$
This axiom schema is part of the trusted baseline and is used to derive
specification-style constant introduction.

*Constraint (No Shadowing of Reserved Symbols).*
For every scope stack state $S$, insertion is forbidden for reserved names:
$
  (" "c in "Reserved" " ")
  /
  (S tack.r "add"(c : tau) mapsto "fail")
$
where currently $"Reserved" = {"=", "@"}$.

*Definition (Typed Equality Formation).*
Given resolved terms $u, v$:
$
  (" "Gamma tack.r.r u : tau ," "Gamma tack.r.r v : tau" ")
  /
  (Gamma tack.r.r (u = v) : "bool")
$
This formation rule is the unique source of equality propositions used by primitive rules.

*Remark (Signature Separation).*
Ordinary entries in $Sigma_c$ are user/system constants. Logical equality is fixed by the logic layer and cannot be rebound by scope operations.

== Signature Judgments for Scoped Stacks

*Definition (Scoped Signature Judgments).*
We use the following judgments for scoped signature operations:

- $S tack.r "wf"$: signature stack $S$ is well-formed.
- $S tack.r c : tau$: lookup for constant $c$ succeeds with type $tau$.
- $S tack.r "push" mapsto S'$: push succeeds and returns $S'$.
- $S tack.r "add"(c : tau) mapsto S'$: insertion in current scope succeeds.
- $S tack.r "pop" mapsto S'$: pop succeeds and returns $S'$.

Notation: $S "++" [F]$ denotes stack append with $F$ as the new innermost frame. In particular, $S "++" ["empty"]$ means push one fresh empty scope onto $S$.

Representative rules:

$
  (S tack.r "wf")
  /
  (" "S tack.r "push" mapsto S "++" ["empty"]" ")
$

$
  (" "S = [S_0, ..., S_n] , c ∉ "dom"(S_n) , S' = [S_0, ..., S_n[c := tau]]" ")
  /
  (S tack.r "add"(c : tau) mapsto S')
$

$
  (" "S = [S_0, ..., S_n] , c in "dom"(S_n) , S_n(c) = tau" ")
  /
  (S tack.r c : tau)
$

$
  (" "S = [S_0, ..., S_n] , c ∉ "dom"(S_n) , [S_0, ..., S_(n - 1)] tack.r c : tau" ")
  /
  (S tack.r c : tau)
$

$
  (" "S = [S_0, ..., S_n] , n > 0 , S' = [S_0, ..., S_(n - 1)]" ")
  /
  (S tack.r "pop" mapsto S')
$

*Well-Formedness Side Conditions.*

- no frame may bind a reserved logical symbol;
- each frame is a finite partial map;
- lookup is deterministic by innermost-first traversal.

These rules make success/failure boundaries explicit and align the scoped stack API with a judgmental presentation.

== Global Theory State vs Local Scope State

To avoid ambiguity between poppable lookup state and persistent logical commitments, QED distinguishes two state layers:

- global theory state $T$: append-only logical history (definition heads, type constructors, proved definitional theorems);
- local scope stack $S$: poppable name-lookup convenience layer.

Combined machine state is written $(T, S)$.

Operational boundary:

1. `push`/`pop` mutate $S$ only.
2. definitional extension mutates $T$ (and may expose a binding in current $S$).
3. global freshness checks for definitions are performed against $T$, never against current-stack-only visibility.

Name history used by definitions:
$
  "DefHeads"(T) = {"all constant names ever committed by definitional extension"}
$

Equivalent implementation view: `"DefHeads"(T)` can be realized as a monotone global registry/tombstone set that is not affected by scope pop.

Monotonicity law:
$
  T mapsto T' => "DefHeads"(T) ⊆ "DefHeads"(T')
$

*Proposition (Pop Invariance of Definitional History).*
If $(T_0, S) tack.r "pop" mapsto (T_1, S')$, then
$
  T_0 = T_1 ∧ "DefHeads"(T_0) = "DefHeads"(T_1)
$
trivially, because `pop` is local-scope-only and does not rollback committed theory symbols.

== Type Grammar

Types are generated by the grammar
$
  tau ::= alpha | k(tau_1, ..., tau_n)
$
where $alpha$ ranges over type variables and $k in Sigma_t$ with $a(k) = n$.

In implementation terms, QED uses:

- `TyVal(name)` for type variables.
- `TyApp(tycon, args)` for constructor application.

This representation is syntax-directed and supports recursive operations such as type substitution and constructor decomposition.

== Type Constructor Extension Discipline

Non-emptiness of all well-formed types is enforced by admissible type introduction, not by unconstrained signature mutation.

*Definition (Type Definition Admissibility).*
A new type-constructor introduction is written:
$
  "TypeDefOK"(T, k, a, "Rep", P, w)
$
and requires:

1. $k ∉ "TySymbols"(T)$ and $a$ matches declared parameter arity.
2. $w$ is a witness theorem establishing representability non-emptiness for each parameter instantiation.
3. the defining predicate $P$ is well-typed and closed under the declared parameters.
4. all free type variables of $P$ are exactly the declared parameters (no undeclared type-variable leakage).
5. representation head name $"Rep"_k$ is globally fresh in theory history and reserved-symbol disjoint.
6. abstraction head name $"Abs"_k$ is globally fresh in theory history and reserved-symbol disjoint.

Representative admissible step:
$
  "TypeDefOK"(T, k, a, "Rep", P, w) => T mapsto T + {"typedef" k / a}
$

*Definition (Typedef Product Contract).*
For each admissible typedef step above, theory extension must also expose fresh constants:
$
  "Abs"_k : "RepTy"_k -> k(alpha_1, ..., alpha_a)
$
$
  "Rep"_k : k(alpha_1, ..., alpha_a) -> "RepTy"_k
$
and must provide the following theorem schemata (with the declared type parameters explicitly quantified):

1. Surjectivity of abstraction:
$
  tack.r forall n : k(alpha_1, ..., alpha_a). "Abs"_k("Rep"_k(n)) = n
$
2. Representation range soundness:
$
  tack.r forall n : k(alpha_1, ..., alpha_a). P("Rep"_k(n))
$
3. Conditional retraction on predicate range:
$
  tack.r forall r : "RepTy"_k. P(r) => "Rep"_k("Abs"_k(r)) = r
$

No weaker contract is admissible for kernel-level typedef extension.

*Construction Invariant (No Empty-Type Escape).*
If base prelude types are non-empty and every later type-constructor extension satisfies `"TypeDefOK"`, then every well-formed type over the resulting signature has a non-empty semantic carrier.

This invariant is the syntactic enforcement hook used by `INST_TYPE` soundness arguments.

== Term Grammar

Terms are generated by:

$
  t ::= & x : tau             && " variable" \
      | & c : tau             && " constant" \
      | & t_1" "t_2           && " application" \
      | & lambda (x : tau). t && " abstraction"
$

where $x$ is a variable symbol and $c$ is a constant symbol.

In implementation terms, QED uses:

- `Var(name, tau)`
- `Const(name, tau)`
- `Comb(f, x)`
- `Abs(x, t)`

The abstraction constructor is intended to bind occurrences of the variable component of `x` in `t`.

#keyblock("warning", [Binding and Capture], [
  Any substitution algorithm used by the kernel must be capture-avoiding. This is not a convenience detail: it is a semantic requirement for soundness.
])

== Resolution Boundary (Integrated Form)

*Definition (One-Shot Resolution).*
To avoid splitting the document into two full grammars, QED keeps one named grammar and adds a single boundary judgment:
$
  Sigma_c tack.r t mapsto t_r
$
where $t_r$ is a resolved term used by kernel rules. Constant occurrences are frozen at resolution time and are not re-looked-up during later theorem reuse.

Notation compatibility: this section writes resolution with $mapsto$; the later typing section writes the same elaboration relation as $⇓$.

Representative constant-resolution clause:
$
  (Sigma_c tack.r c : tau , "resolve"(Sigma_c, c) = kappa_c)
  /
  (Sigma_c tack.r c : tau mapsto "ConstAtom"(kappa_c, tau))
$

*Property (Theorem Stability Under Scope Mutation).*
If a theorem is constructed from resolved terms, then later `push`/`pop`/shadowing operations on $Sigma_c$ do not change that theorem's meaning or typing status.

*Property (Alias Safety for Existing Theorems).*
Theorem aliasing is handle-level only: alias creation does not trigger re-elaboration, and therefore does not depend on the current signature stack.

= Elaboration and Core Typing Judgments

To make scope-mutation stability and boundary safety derivable (not merely stated), QED uses a two-layer typing story.

== Named Elaboration Judgment

Named terms are first elaborated against the current signature stack:
$
  Sigma_c ; Gamma tack.r t ⇓ t_r
$
where $t_r$ is a resolved term in which constant occurrences have fixed kernel identities.

Representative clauses:

$
  (" "(x : tau) in Gamma" ")
  /
  (Sigma_c ; Gamma tack.r x : tau ⇓ "RVar"(x, tau))
$

$
  (" "Sigma_c tack.r c : tau_"gen" , "resolve"(Sigma_c, c) = kappa_c , tau ≼ tau_"gen"" ")
  /
  (Sigma_c ; Gamma tack.r c : tau ⇓ "RConst"(kappa_c, tau))
$

$
  (" "Sigma_c ; Gamma tack.r f ⇓ f_r ," "Sigma_c ; Gamma tack.r x ⇓ x_r" ")
  /
  (Sigma_c ; Gamma tack.r f" "x ⇓ "RComb"(f_r, x_r))
$

$
  (" "Sigma_c ; (Gamma, x : tau) tack.r t ⇓ t_r" ")
  /
  (Sigma_c ; Gamma tack.r λ(x : tau). t ⇓ "RAbs"(x, tau, t_r))
$

Elaboration failure is explicit and does not produce a theorem object.

== Core Typing over Resolved Terms

Primitive rules consume resolved terms only. Their typing judgment is:
$
  Gamma tack.r.r t_r : tau
$
with rules independent of mutable signature lookup.

Representative clauses:

$
  (" "(x : tau) in Gamma" ")
  /
  (Gamma tack.r.r "RVar"(x, tau) : tau)
$

$
  (" "kappa_c : tau_"gen" , tau ≼ tau_"gen"" ")
  /
  (Gamma tack.r.r "RConst"(kappa_c, tau) : tau)
$

$
  (" "Gamma tack.r.r f_r : "fun"(tau_1, tau_2) ," "Gamma tack.r.r x_r : tau_1" ")
  /
  (Gamma tack.r.r "RComb"(f_r, x_r) : tau_2)
$

$
  (Gamma, x : tau_1 tack.r.r t_r : tau_2)
  /
  (" "Gamma tack.r.r "RAbs"(x, tau_1, t_r) : "fun"(tau_1, tau_2)" ")
$

*Lemma (Polymorphic Constant Instantiation Admissibility).*
If $kappa_c : tau_"gen"$ and $tau ≼ tau_"gen"$, then `"RConst"(kappa_c, tau)` is a well-formed resolved term and may appear in any rule premise requiring type $tau$.

*Remark (No Monomorphic Lockout).*
A constant introduced once at principal schema (e.g. $"fun"(alpha, alpha)$) is usable at all admissible instances (e.g. $"fun"("bool", "bool")$, $"fun"("int", "int")$), rather than requiring one separately named constant per instance type.

== Stability Theorem for Scope Mutation

*Theorem (Resolved-Theorem Stability Under Scope Mutation).*
If $Sigma_c ; Gamma tack.r t ⇓ t_r$ and $Gamma tack.r.r t_r : tau$, then for any later signature stack mutation sequence $mu$ (push/pop/shadowing on non-reserved names), the established typing fact for $t_r$ remains valid:
$
  Gamma tack.r.r t_r : tau
$
because $t_r$ contains fixed resolved constant identities and does not re-run named lookup.

This theorem is the formal bridge behind one-shot resolution stability claims.

= Substitution and Alpha-Equivalence

== Type Substitution

Type substitution is a mapping `theta : type_variable -> hol_type` that extends structurally to types and terms.

For a type variable $alpha$,

- $theta(alpha)$ if defined,
- otherwise $alpha$.

For type application $k(tau_1, ..., tau_n)$,

- apply $theta$ recursively to each argument.

== Term Substitution

Term substitution is a finite map from variables to terms. It must satisfy two constraints:

1. Type preservation: replacement terms match the declared type of replaced variables.
2. Capture avoidance: bound variables may require renaming before substitution under abstraction.

== De Bruijn Shifting (for `BETA`)

The De Bruijn core is typed. Binder-domain type labels are part of core syntax and are never erased.

Core grammar fragment:
$
  d ::= "DBound"(k, tau) | "DFree"(x, tau) | "DConst"(c, tau) | "DComb"(d_1, d_2) | "DAbs"(tau, d)
$

To make beta operationally precise, we fix two recursive operators on typed De Bruijn terms: `shift` and `subst`.

For shift, written $"shift"(delta, c, d)$ with increment $delta$ and cutoff $c$:

- $"shift"(delta, c, "DBound"(k, tau)) = "DBound"(k, tau)$, when $k < c$.
- $"shift"(delta, c, "DBound"(k, tau)) = "DBound"(k + delta, tau)$, when $k >= c$.
- $"shift"(delta, c, "DComb"(f, x)) = "DComb"("shift"(delta, c, f), "shift"(delta, c, x))$.
- $"shift"(delta, c, "DAbs"(tau, t)) = "DAbs"(tau, "shift"(delta, c + 1, t))$.

For substitution, written $"subst"(j, s, d)$:

- $"subst"(j, s, "DBound"(k, tau)) = s$, when $k = j$ and $"type_of"(s) = tau$.
- $"subst"(j, s, "DBound"(k, tau)) = "DBound"(k, tau)$, when $k != j$.
- $"subst"(j, s, "DComb"(f, x)) = "DComb"("subst"(j, s, f), "subst"(j, s, x))$.
- $"subst"(j, s, "DAbs"(tau, t)) = "DAbs"(tau, "subst"(j + 1, "shift"(1, 0, s), t))$.

Then the typed De Bruijn beta contraction used by the kernel is fixed as
$
  "beta"(("DAbs"(tau, t)) u) = "shift"(-1, 0, "subst"(0, "shift"(1, 0, u), t))
$
with the side condition $"type_of"(u) = tau$.

*Invariant (Typed-Core Injectivity).*
De Bruijn structural equality is type-sensitive:
$
  "DAbs"(tau_1, t_1) = "DAbs"(tau_2, t_2) => tau_1 = tau_2 ∧ t_1 = t_2
$
Hence abstractions that differ only by binder-domain type are distinct core terms and cannot be merged by structural matching.

== Alpha-Equivalence

Alpha-equivalence, written $t_1 equiv_alpha t_2$, identifies terms up to systematic renaming of bound variables. It is required by multiple kernel operations, including theorem transitivity-style checks where structural syntax should not distinguish alpha-variants.

The specification uses the following mandatory properties:

1. Reflexive: $t equiv_alpha t$.
2. Symmetric: $t_1 equiv_alpha t_2 => t_2 equiv_alpha t_1$.
3. Transitive: $t_1 equiv_alpha t_2 ∧ t_2 equiv_alpha t_3 => t_1 equiv_alpha t_3$.
4. Congruence for constructors (`Comb`, `Abs`) and proposition/equality contexts.

For De Bruijn forms, structural equivalence $tilde.equiv$ is used as the canonical representative-level equality. The boundary lemmas below connect $equiv_alpha$ and $tilde.equiv$.

= Boundary Conversion and Scoped Shadowing

QED currently uses a two-layer boundary:

- external-facing terms/theorems are in named syntax;
- kernel rule cores execute on De Bruijn syntax.

Boundary conversion functions are used with the following Haskell-style signatures:

$
  "Term"_arrow.b :: "Term" arrow.r "DbTerm"?
$
$
  "Term"_arrow.t :: "DbTerm" arrow.r "Term"?
$
$
  "Thm"_arrow.b :: "Thm" arrow.r "DbSequent"?
$
$
  "Thm"_arrow.t :: "DbSequent" arrow.r "Thm"?
$

Here $"Term"_arrow.b$ lowers named terms to De Bruijn terms, and $"Term"_arrow.t$ reconstructs named terms from De Bruijn terms. Likewise, $"Thm"_arrow.b$ lowers named sequents to De Bruijn sequents, and $"Thm"_arrow.t$ lifts De Bruijn sequents back to named boundary objects. All four conversions are partial and may fail at the boundary.

For theorem objects:
$
  "Thm"_arrow.b" "A_p tack.r p = A_d tack.r p_d
$
and
$
  "Thm"_arrow.t" "A_d tack.r p_d = A_p' tack.r p'
$
defined pointwise by $"Term"_arrow.b$ and $"Term"_arrow.t$ on assumptions and conclusion.

== Boundary Conversion Properties

The kernel implementation relies on the following invariants.

*Lemma (Alpha-Invariant Lowering).*
$
  (t_1 equiv_alpha t_2)
  /
  (" Term"_arrow.b" "t_1 tilde.equiv "Term"_arrow.b" "t_2" ")
$

*Lemma (Round-Trip Stability up to Alpha).*
$
  (" Term"_arrow.b" "t mapsto d ," Term"_arrow.t" "d mapsto t'" ")
  /
  (t' equiv_alpha t)
$

*Lemma (Lift Choice Congruence).*
If $"Term"_arrow.t" "d mapsto t_1$ and $"Term"_arrow.t" "d mapsto t_2$, then $t_1 equiv_alpha t_2$.

*Property (Name-Insensitive Rule Matching).*
Any named-side premise matching required by primitive rules is interpreted modulo $equiv_alpha$. Binder spellings are presentation-level choices and cannot change rule applicability.

*Lemma (Type-Sensitive Core Matching).*
Boundary lowering preserves binder-domain type labels. Therefore, if two named abstractions differ in binder-domain type, their lowered typed De Bruijn forms are not structurally equal:
$
  "Term"_arrow.b" "(λ(x : tau_1). t_1) != "Term"_arrow.b" "(λ(y : tau_2). t_2)
$
whenever $tau_1 != tau_2$, even if bodies are De Bruijn-index isomorphic.

*Lemma (Term Denotation Preservation Across Boundary).*
If $"Term"_arrow.b" "t mapsto d$, then for every valuation/model pair $(rho, M)$:
$
  ⟦t⟧_(rho, M) = ⟦d⟧_(rho, M)
$
where the right-hand side denotes De Bruijn evaluation under the environment induced by $rho$.

*Lemma (Sequent Denotation Preservation Across Boundary).*
If $"Thm"_arrow.b" "A_p tack.r p mapsto A_d tack.r p_d$, then semantic validity is preserved:
$
  (A_p tack.r p) " valid " <=> (A_d tack.r p_d) " valid "
$

*Theorem (Semantic Rule Lifting Safety).*
Assume a primitive core rule
$
  R_d : "DbSequent"^n arrow.r "DbSequent"?
$
is semantically preserving on its defined domain:
$
  "valid"(x_d) => "valid"(R_d(x_d))
$
Then the lifted named rule
$
  R" "x = "Thm"_arrow.t" "(R_d" "("Thm"_arrow.b" "x))
$
is semantically preserving on all inputs where boundary conversions succeed. Consequently, rule lifting preserves both structure (modulo alpha) and denotation.

*Property (Diagrammatic Commutation on Successful Conversions).*
The lifting relation is visualized by the following commutative diagram (structural and semantic commutation):

#align(center)[
  #diagram(
    node((0, 1.6), [$"NamedSequent" "/" equiv_alpha$]),
    node((2.0, 1.6), [$"NamedSequent" "/" equiv_alpha$]),
    node((0, 0), [$"DbSequent" "/" tilde.equiv$]),
    node((2.0, 0), [$"DbSequent" "/" tilde.equiv$]),
    edge((0, 1.6), (2.0, 1.6), "->", [$R$]),
    edge((0, 0), (2.0, 0), "->", [$R_d$]),
    edge((0, 1.6), (0, 0), "->", [$"Thm"_arrow.b$]),
    edge((2.0, 0), (2.0, 1.6), "->", [$"Thm"_arrow.t$]),
  )
]

Operationally, this means:
$
  (" Thm"_arrow.b" "x mapsto x_d ," "R_d" "x_d mapsto y_d ," Thm"_arrow.t" "y_d mapsto y" ")
  /
  (R" "x mapsto y)
$
on all inputs where boundary conversions and core rule execution succeed, together with
$
  "valid"(x) => "valid"(y)
$
under the denotation-preservation lemmas above.

*Remark (Not a Strict Bijection).*
This correspondence is not a strict named-to-De Bruijn bijection:

- alpha-variant named terms collapse to one De Bruijn equivalence class;
- lifting from De Bruijn chooses a representative named binder presentation;
- boundary conversions are partial, so the mapping is defined only on well-formed successful cases.

#keyblock("info", [Boundary Discipline], [
  Primitive rules are implemented on `DbSequent`. Named `Thm` values are boundary objects. Conversion failure is treated as boundary failure, not as logical success.
])

== Scoped Shadowing Properties

Let a signature state be a stack
$
  S = [S_0, S_1, ..., S_n]
$
where $S_n$ is the innermost scope.

Notation and intent:

- $P(S)$ denotes pushing a fresh, empty scope.
- $A(S, c : tau)$ denotes inserting a constant into the current scope.
- $Q(S)$ denotes popping the innermost scope.

These operators are the logical counterparts of scope push/add/pop in the implementation.

Lookup is defined by:
$
  L(S, c) = S_j(c)
$
where $j$ is the greatest index such that $c in "dom"(S_j)$.

Insertion in current scope:
$
  A(S, c : tau)
$
is allowed iff $c ∉ "dom"(S_n)$.

From these definitions:

*Proposition (Shadowing Determinism).*
if $c$ is defined in innermost scope $S_n$, then $L(S, c) = S_n(c)$.
Proof sketch: lookup chooses the greatest index $j$ with $c in "dom"(S_j)$; if $c in "dom"(S_n)$, maximality forces $j = n$.

*Proposition (Outer Restoration by Pop).*
if $S' = P(S)$, $A(S', c : tau_1) = S''$, and $Q(S'') = S$, then $L(S, c) = L(Q(S''), c)$.
Proof sketch: insertion in the pushed scope only affects the temporary innermost frame; after pop, stack shape and all outer mappings are restored.

*Proposition (Scope-Local Uniqueness).*
if $c$ is already defined in innermost scope $S_n$, then $A(S, c : tau)$ fails.
Proof sketch: insertion side condition requires $c ∉ "dom"(S_n)$; violating this condition blocks the rule.

These properties specify the intended behavior of `sig_push_scope`, `sig_pop_scope`, `sig_lookup_const`, and scoped insertion APIs.

Scope-local shadowing properties above are lookup properties only. They do not authorize redefining committed definition heads recorded in `"DefHeads"(T)`.

= Theorem Object and Trust Boundary

A theorem is represented mathematically as a sequent
$
  Gamma_p tack.r p
$
with $p$ a boolean term and $Gamma_p$ a finite set of boolean assumptions.

== Assumption Sets as Alpha-Quotients

To keep rule behavior binder-name invariant, assumptions are not raw syntax sets. They are finite sets of alpha-equivalence classes:
$
  Gamma_p ⊆ "Term" "/" equiv_alpha
$
with all elements constrained to type $"bool"$.

Operations used by primitive rules are interpreted on equivalence classes:

- membership: $[a]_alpha in Gamma_p$;
- union: $Gamma_1 union Gamma_2$ on classes;
- removal: $Gamma_p - {[a]_alpha}$.

Required laws:

1. Idempotence: $Gamma union Gamma = Gamma$.
2. Commutativity: $Gamma_1 union Gamma_2 = Gamma_2 union Gamma_1$.
3. Alpha-compatibility of membership/removal:
  if $a equiv_alpha b$ then $[a]_alpha = [b]_alpha$ and
  $
    (Gamma - {[a]_alpha}) = (Gamma - {[b]_alpha})
  $
4. Finiteness preservation under union/removal.

All assumption-manipulating rules (`ASSUME`, `TRANS`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`) are read in this quotient semantics.

The trusted boundary condition is:

- external modules cannot directly construct theorem values,
- theorem values are produced only by primitive kernel inference functions.
- theorem values store resolved terms; primitive rules and theorem aliases do not re-run constant lookup against the current signature stack.

This boundary is the core LCF invariant.

#keyblock("critical", [Kernel Integrity Condition], [
  If external code can fabricate theorem values, the entire soundness argument collapses, regardless of how correct individual inference rules appear.
])

= Definitional Extension Discipline (Conservativity Gate)

QED permits signature growth only through conservative admissible extension gates.

*Rule Schema (New Constant by Definition).*
Given base theory $T$ and fresh constant $c$:
$
  (" "c ∉ "DefHeads"(T) , c ∉ "Reserved" , Gamma tack.r r : tau , "closed"(r, Gamma = "empty") , "acyclic"(r, c) , "TVars"(r) ⊆ "TVars"(tau)" ")
  /
  (T mapsto T + {"def" c : tau = r})
$

Mandatory side conditions:

1. *Freshness*: $c$ does not occur in global definitional history `"DefHeads"(T)` and is not reserved.
2. *Typedness*: $r$ is well-typed at declared type $tau$.
3. *Closedness*: $r$ has no free term variables (global-definition discipline).
4. *Non-circularity*: $r$ does not mention $c$ (directly or via definitional cycle).
5. *Type-Variable Closure*: free type variables in $r$ are constrained by the declared head type:
  $
    "TVars"(r) ⊆ "TVars"(tau)
  $
  so no ghost type variable can appear only in the body.

*Safety Note (Ghost Type Variables).*
Without Condition 5, an `INST_TYPE` step may change only the definition body instance while leaving the head constant unchanged, which breaks definitional conservativity.

*Policy Clarification (Shadowing vs Definitional Freshness).*
Scoped insertion rules may allow same-name shadowing for ordinary local constants. Definitional extension is stricter: definitional heads are introduced with globally fresh names and are never shadow-reused. This resolves any apparent tension between local scope shadowing and global definition soundness.

*Theorem (Conservativity of Definitional Extension).*
Let $T'$ be obtained from $T$ by one admissible definitional extension above. For every theorem statement $p_0$ in the old language of $T$:
$
  T' tack.r p_0 => T tack.r p_0
$
Hence new definitions add abbreviatory power without increasing provability over the old signature.

== Definition Admissibility Judgment

To make the definition gate reusable by later rules and metatheory, we package side conditions into one judgment:
$
  "DefOK"(T, c : tau = r)
$
defined as the conjunction of Conditions 1--5 above.

Admissible extension step:
$
  "DefOK"(T, c : tau = r) => T mapsto T + {"def" c : tau = r}
$

*Lemma (Definition Theorem Shape).*
If $"DefOK"(T, c : tau = r)$ and $T mapsto T'$, then the generated definition theorem has empty assumptions:
$
  tack.r c = r
$
and is well-typed at $"bool"$.

*Lemma (Instantiation Coherence for Definitions).*
If $"DefOK"(T, c : tau = r)$ and $theta$ is any admissible type substitution on $"TVars"(tau)$, then
$
  theta(c = r) = theta(c) = theta(r)
$
and no body-only type variable can be changed independently of the head.

*Corollary (No Ghost-Type Instantiation Drift).*
Under $"DefOK"$, `INST_TYPE` cannot produce contradictory definition instances of one constant by varying a type variable that appears only in the body.

This subsection is the structural contract tying definitional extension to the primitive `INST_TYPE` rule.

= Controlled Specification Extension Discipline

To support HOL-style derived-theory construction without unrestricted axiom injection,
QED treats specification introduction as a derived discipline over Choice + `DefOK`,
not as an independent primitive inference rule.

*Definition (Specification Admissibility).*
Given theory $T$, fresh constant head $c$, and predicate $P(x)$, write:
$
  "SpecOK"(T, c : tau, P)
$
iff all conditions below hold:

1. Freshness: $c ∉ "DefHeads"(T)$, $c ∉ "Reserved"$, and $c$ is not already in theory symbol tables.
2. Witness theorem shape: there exists a theorem with empty assumptions ($Gamma = "empty"$):
  $
    tack.r exists x : tau. P(x)
  $
3. Term closure: $P(x)$ has no free term variable except $x$.
4. Type-variable closure:
  $
    "TVars"(P) ⊆ "TVars"(tau)
  $
  (no type variable appears in $P$ that is absent from the declared type of $c$).
5. Strict type-schema lock:
  $
    "Schema"(c) = "Gen"(tau)
  $
  for this admission step only.
6. No implicit widening:
  no type variable absent from $tau$ may be generalized into $"Schema"(c)$ by this step.

*Derived Rule Schema (Specification via Choice + Definitional Admission).*
$
  (" "tack.r exists x : tau. P(x) , "SpecOK"(T, c : tau, P) , "DefOK"(T, c : tau = "@"(lambda x : tau. P(x)))" ")
  /
  (T mapsto T + {"def" c : tau = "@"(lambda x : tau. P(x))} , tack.r P(c))
$

This is the only admissible introduction path for specification constants in this stage.

*Meta-Constraint (No Hidden Side Conditions).*
Any implementation-level check used by `SpecOK` must correspond to one of the six
explicit conditions above; no additional silent premise is allowed.

*Theorem Goal (Conservativity of Specification Extension).*
If $T'$ is obtained from $T$ by one admissible `SpecOK` step and $phi$ is a sentence
in the old language of $T$, then:
$
  T' tack.r phi => T tack.r phi
$
This is a mandatory proof obligation for the specification gate design.

= Global Admissibility Envelope

The kernel-level soundness argument uses a single admissibility envelope:

1. theorem values arise only from primitive rules or admissible extension gates;
2. primitive rules consume well-formed resolved sequents;
3. definitional extension steps must satisfy `"DefOK"`;
4. type-constructor extension steps must satisfy `"TypeDefOK"` (non-emptiness witness gate);
5. specification extension steps must satisfy `"SpecOK"` (derived over Choice + `DefOK`);
6. boundary conversion failures are non-derivational failures.

All later soundness obligations are stated relative to this envelope, so no rule silently bypasses definition admissibility constraints.

= Primitive Inference Rules

QED follows a HOL Light style primitive interface:

`REFL`, `ASSUME`, `TRANS`, `MK_COMB`, `ABS`, `BETA`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST_TYPE`, `INST`.

Judgmental convention in this section:

- core rule premises are checked on resolved terms/sequents;
- named forms are boundary presentations of those same rules;
- assumption-set operations are interpreted on alpha-quotient classes.

Each primitive rule must be specified by:

1. Input theorem and term constraints.
2. Side conditions (typing, freeness, alpha-matching, etc.).
3. Output sequent.
4. Failure condition classification.

For example, selected rules can be presented in antecedent style:

- `REFL`: for any term $t$, conclude $tack.r t = t$.
- `ASSUME`: for any boolean proposition $p$, conclude $p tack.r p$.

$
  (" "A_p tack.r s = t ," "B_p tack.r t = u" ")
  /
  (A_p union B_p tack.r s = u)
$

$
  (" "A_p tack.r p = q ," "B_p tack.r p" ")
  /
  (A_p union B_p tack.r q)
$

Detailed formal side conditions are maintained in parallel with implementation updates.

== Rule Schema: `REFL`

Input:

- a well-formed term $t$.

Output:

- theorem $tack.r t = t$.

Side conditions:

1. $t$ must be typable.
2. equality constructor must be formed at the type of $t$.

Failure clauses:

1. malformed term input;
2. type construction failure in equality formation.

Antecedent form:
$
  (" "Gamma tack.r.r t_r : T" ") / (tack.r t_r = t_r)
$

== Rule Schema: `ASSUME`

Input:

- a proposition term $p$.

Output:

- theorem $p tack.r p$.

Side conditions:

1. $p$ must have type $"bool"$.
2. assumption set representation must admit $p$.

Failure clauses:

1. non-boolean proposition;
2. invalid assumption-set insertion.

Antecedent form:
$
  (" "Gamma tack.r.r p_r : "bool " ," "[p_r]_alpha in Gamma_p" ")
  /
  (" "Gamma_p tack.r p_r" ")
$

== Rule Schema: `TRANS`

Input:

- theorem $A_p tack.r s = t$;
- theorem $B_p tack.r t = u$.

Output:

- theorem $A_p union B_p tack.r s = u$.

Side conditions:

1. both conclusions must be equalities;
2. the middle terms must match up to alpha-equivalence and type consistency;
3. under boundary lowering, core matching is performed on typed De Bruijn terms (including binder-domain labels), not on type-erased structure.

Failure clauses:

1. non-equality conclusion in either premise theorem;
2. middle-term mismatch;
3. type inconsistency in chained equality;
4. boundary/core mismatch caused by typed-core inequality.

Antecedent form:
$
  (" "A_p tack.r s = t ," "B_p tack.r t = u" ")
  /
  (A_p union B_p tack.r s = u)
$

== Rule Schema: `MK_COMB`

Input:

- theorem $A_p tack.r f = g$;
- theorem $B_p tack.r x = y$.

Output:

- theorem $A_p union B_p tack.r f x = g y$.

Side conditions:

1. both premise conclusions must be equalities;
2. $f$ and $g$ must have function type with argument type matching $x$ and $y$;
3. codomain types of $f$ and $g$ must coincide.

Failure clauses:

1. non-equality premise theorem;
2. function-domain mismatch for application;
3. codomain inconsistency across the two function sides.

Antecedent form:
$
  (" "A_p tack.r f = g ," "B_p tack.r x = y" ")
  /
  (A_p union B_p tack.r f x = g y)
$

== Rule Schema: `ABS`

Input:

- variable term $x$;
- theorem $A_p tack.r s = t$.

Output:

- theorem $A_p tack.r λ (x : tau). s = λ (x : tau). t$.

Side conditions:

1. $x$ must be a variable term;
2. premise conclusion must be an equality;
3. $x$ must not occur free in assumptions $A_p$.

Failure clauses:

1. non-variable abstraction binder;
2. non-equality premise theorem;
3. free-variable violation in assumption set.

Antecedent form:
$
  (A_p tack.r s = t)
  /
  (" "A_p tack.r λ (x : tau). s = λ (x : tau). t" ")
$

== Rule Schema: `BETA`

Input:

- a typed De Bruijn beta-redex term of shape $("DComb"("DAbs"(tau, t), u))$.

Output:

- theorem $tack.r ("DComb"("DAbs"(tau, t), u)) = "beta"(("DAbs"(tau, t)) u)$.

This is the De Bruijn substitution form (with the usual shift and shift-back to avoid capture). It corresponds to the named rule $tack.r ((λ (x : tau). s) u) = s[u\/x]$ under boundary conversion.

Side conditions:

1. the redex must be well-typed;
2. substitution is capture-avoiding;
3. the contracted De Bruijn term must be well-scoped, so the final $"shift"(-1, 0, ...)$ step is defined.
4. the argument type must equal the abstraction binder-domain label: $"type_of"(u) = tau$.

*Lemma (Well-Scoped Beta Contraction Safety).*
For well-typed and well-scoped input redexes, the contraction
$
  "beta"(("DAbs"(tau, t)) u) = "shift"(-1, 0, "subst"(0, "shift"(1, 0, u), t))
$
does not create dangling indices.

Failure clauses:

1. input is not a beta-redex of the required shape;
2. type inconsistency in redex construction;
3. boundary reconstruction failure;
4. binder-domain label mismatch in typed De Bruijn core.

Antecedent form:
$
  (" "r = "DComb"("DAbs"(tau, t), u) , "welltyped"(r) , "type_of"(u) = tau" ")
  /
  (tack.r r = "beta"("DComb"("DAbs"(tau, t), u)))
$

== Rule Schema: `EQ_MP`

Input:

- theorem $A_p tack.r p = q$;
- theorem $B_p tack.r p$.

Output:

- theorem $A_p union B_p tack.r q$.

Side conditions:

1. first premise must conclude an equality proposition;
2. left side of equality must match the second premise conclusion up to alpha-equivalence;
3. all involved terms must be boolean propositions.

Failure clauses:

1. first premise is not an equality theorem;
2. proposition mismatch between equality lhs and premise theorem;
3. non-boolean proposition in premises.

Antecedent form:
$
  (" "A_p tack.r p = q ," "B_p tack.r p" ")
  /
  (A_p union B_p tack.r q)
$

== Rule Schema: `DEDUCT_ANTISYM_RULE`

Input:

- theorem $A_p tack.r p$;
- theorem $B_p tack.r q$.

Output:

- theorem $(A_p - {q}) union (B_p - {p}) tack.r p = q$.

Side conditions:

1. both premises must conclude propositions;
2. subtraction from assumption sets must be defined by alpha-aware proposition equality;
3. resulting assumption set must remain finite.

Failure clauses:

1. malformed assumption-set subtraction;
2. proposition mismatch in set-removal targets;
3. non-propositional premise conclusion.

Antecedent form:
$
  (A_p tack.r p ," "B_p tack.r q)
  /
  (" "(A_p - {q}) union (B_p - {p}) tack.r p = q" ")
$

== Rule Schema: `INST_TYPE`

Input:

- type substitution $theta$;
- theorem $A_p tack.r p$.

Output:

- theorem $theta(A_p) tack.r theta(p)$.

Side conditions:

1. substitution domain must contain only type variables;
2. every target type in $theta$ must be a well-formed type admitted by the current type-extension discipline (`TypeDefOK`-closed theory state);
3. substitution application must preserve term well-typedness;
4. if the theorem being instantiated is a definitional theorem produced under `DefOK`, the instantiated head/body pair must satisfy definitional instantiation coherence (no body-only type drift);
5. for every constant occurrence `"RConst"(kappa_c, tau_i)` in the theorem, instantiated type arguments must still satisfy $tau_i ≼ tau_"gen"(kappa_c)$;
6. theorem structure must be preserved under parallel type substitution.

Failure clauses:

1. invalid substitution mapping (non-type-variable key or malformed target type);
2. inadmissible type target (violates current type-admissibility gate);
3. typing failure after substitution;
4. definitional coherence violation for definition-origin theorems;
5. constant-instance mismatch against principal schema;
6. malformed theorem structure under substitution.

Antecedent form:
$
  (" "A_p tack.r p , "valid_ty_subst"(theta) , "admissible_ty_image"(T, theta) , "def_inst_coherent"(theta, A_p tack.r p) , "const_instance_ok"(theta, A_p tack.r p)" ")
  /
  (theta(A_p) tack.r theta(p))
$

*Bridge Note.*
This rule is soundness-linked to three upstream contracts:

- definition admissibility (`DefOK`) prevents ghost-type-variable drift under instantiation;
- type admissibility (`TypeDefOK`) prevents empty-type semantic escape in substitution targets;
- constant principal-schema instantiation guard (`≼`) permits polymorphic constant use without collapsing type checks;
- global admissibility envelope forbids bypassing either gate during theorem production.

== Rule Schema: `INST`

Input:

- term substitution $sigma$;
- theorem $A_p tack.r p$.

Output:

- theorem $sigma(A_p) tack.r sigma(p)$.

*Definition (Parallel Substitution Snapshot).*
For $sigma = {x_1 mapsto s_1, ..., x_n mapsto s_n}$, substitution is simultaneous: each $s_i$ is read in the original pre-substitution context, and no right-hand side is rewritten by another entry of $sigma$.

Example (Swap Case):
$
  sigma = {x mapsto y, y mapsto x}
$
must exchange $x$ and $y$ in one parallel step, not via sequential chaining.

Side conditions:

1. substitution domain must contain only variable terms;
2. each mapped term in $sigma$ must have the same type as its source variable;
3. substitution must be capture-avoiding and applied in parallel.

Failure clauses:

1. non-variable key in substitution map;
2. type mismatch in substitution pair;
3. variable capture or malformed substitution application.

Antecedent form:
$
  (" "A_p tack.r p ," valid"(sigma)" ")
  /
  (sigma(A_p) tack.r sigma(p))
$

= Soundness Strategy

The project-level soundness story is divided into six obligations.

1. Rule-level preservation: every primitive rule preserves semantic validity.
2. Definition-level conservativity: every constant-definition step used by the kernel satisfies $"DefOK"$ and preserves old-language provability.
3. Type-level non-emptiness preservation: every type-constructor extension satisfies `"TypeDefOK"` so well-formed types remain semantically inhabited.
4. Specification-level conservativity: every specification step satisfies `"SpecOK"` and preserves old-language provability.
5. Interface safety: only primitive rules and admissibility-gated extensions can introduce theorem values.
6. Derivation closure: any finite derivation tree built from primitive rules plus admissible extensions is sound.

This decomposition is practical: it aligns the formal argument with module boundaries and test responsibilities.

Dependency closure for these obligations is now explicit:

- Obligation 1 depends on: core typing, substitution lemmas, alpha-quotient assumptions, and semantic lifting lemmas.
- Obligation 2 depends on: definitional side conditions, type-variable closure, and conservativity theorem.
- Obligation 3 depends on: type-definition witness discipline and non-empty-type construction invariant.
- Obligation 4 depends on: explicit `SpecOK` derived schema over Choice + `DefOK`, freshness/closure constraints, and specification conservativity theorem.
- Obligation 5 depends on: theorem constructor encapsulation + boundary failure discipline + extension gate encapsulation.
- Obligation 6 depends on: induction on derivation depth using Obligations 1, 2, 3, 4, and 5.

== One-Page Soundness Dependency Map (Reader-First)

Instead of one dense graph, we use a layered map read in page order (top -> down).
In this map, each downward arrow means "derives to next layer."

Layer 4 — Foundations (top):

- F1: Signatures + reserved symbols.
- F2: Elaboration + core typing.
- F3: Substitution + alpha laws.
- F4: Explicit infinity-anchor assumption (model-class restriction).
- F5: Primitive choice-operator axiom schema.

Layer 3 — Admissibility Gates:

- A1: Primitive rule schemas + boundary denotation lemmas.
- A2: Definitional admissibility (`DefOK`).
- A3: Type admissibility (`TypeDefOK`).
- A4: Specification admissibility (`SpecOK`, derived over Choice + `DefOK`).

Layer 2 — Preservation Obligations:

- P1: Rule-level preservation.
- P2: Definition conservativity.
- P3: Type non-emptiness preservation.
- P4: Specification conservativity (for derived `SpecOK` admissions).
- P5: Interface safety.

Layer 1 — Global Result (bottom):

- G1: Global derivation soundness.

#align(center)[
  #diagram(
    node((0, 0.0), [Layer 4: Foundations]),
    node((0, 1.0), [Layer 3: Admissibility Gates]),
    node((0, 2.0), [Layer 2: Preservation Obligations]),
    node((0, 3.0), [Layer 1: Global Derivation Soundness]),
    edge((0, 0.0), (0, 1.0), "->"),
    edge((0, 1.0), (0, 2.0), "->"),
    edge((0, 2.0), (0, 3.0), "->"),
  )
]

Review rule: every Layer 1 claim must be traceable upward through Layer 2/3 to Layer 4 foundations.

== Semantic Assumptions

*Assumption (Base Non-Empty Prelude Types).*
Initial built-in types (before user extensions) are interpreted by non-empty semantic carriers.

*Assumption (Explicit Infinity Anchor).*
There exists a distinguished foundation type `"ind"` and a function $f : "ind" -> "ind"$ such that:
$
  "Injective"(f) ∧ ¬"Surjective"(f)
$
This assumption is explicit and is part of the trusted baseline. No hidden implementation
shortcut may replace it.

*Definition (Canonical Infinity-Anchor Theorem Identifier).*
The exported theorem name `"IND_INFINITY_AXIOM"` denotes exactly the sentence:
$
  tack.r exists f : "fun"("ind", "ind"). "Injective"(f) ∧ ¬"Surjective"(f)
$
No alternate theorem shape may be treated as equivalent by implementation policy alone.

*Theorem (Global Non-Empty Type Preservation).*
Given the base assumption above and admissible type-constructor extensions satisfying `"TypeDefOK"`, every well-formed type in the extended signature is interpreted by a non-empty carrier. Consequently, `INST_TYPE` ranges only over non-empty type interpretations.

*Assumption (Classical HOL Model Discipline).*
The soundness argument is read under the standard HOL set-theoretic model discipline: typing and instantiation preserve denotation, and theorem validity is evaluated in that model class.

*Assumption (Choice-Axiom Model Compatibility).*
The model class used for soundness must validate the reserved choice-operator schema
introduced above; specification-derived constants are interpreted through that same
choice-compatible model class.

*Meta-Theorem Target (Global Conservativity Under Admissible Extensions).*
Let $T'$ be obtained from $T$ by a finite sequence of admissible steps from
$
  {"DefOK", "TypeDefOK", "SpecOK"}  " (where SpecOK is derived over Choice + DefOK)"
$
Then for any sentence $phi$ over the old language of $T$:
$
  T' tack.r phi => T tack.r phi
$
This target is normative: any extension design failing this goal is rejected.

== Type Preservation Sketch for `MK_COMB`

*Property (Type Preservation for `MK_COMB`).*
Assume premises $A_p tack.r f = g$ and $B_p tack.r x = y$, with
$
  (" "Gamma tack.r.r f_r : "fun"(tau_1, tau_2) ∧ Gamma tack.r.r g_r : "fun"(tau_1, tau_2) ∧ Gamma tack.r.r x_r : tau_1 ∧ Gamma tack.r.r y_r : tau_1" ")
$
Then by application typing,
$
  (" "Gamma tack.r.r f_r" "x_r : tau_2 ∧ Gamma tack.r.r g_r" "y_r : tau_2" ")
$
and therefore
$
  Gamma tack.r.r (f_r" "x_r = g_r" "y_r) : "bool"
$
So the output proposition in `MK_COMB` is well-typed as a boolean formula, which is exactly the theorem-object invariant.

= Engineering Correspondence

The formal clauses above map to implementation modules as follows.

- `src/kernel/types.mbt`: type constructors, decomposers, predicates, and type-level operators.
- `src/kernel/terms.mbt`: term constructors, decomposers, typing helper, and term-level operators.
- `src/kernel/thm.mbt`: theorem abstraction and primitive rule implementation.
- `src/kernel/sig.mbt`: scoped signature stack, constant registration, and definitional signature operations.

A development task is complete only when the mathematical clause and its implementation clause are both updated.

== Rule-to-Implementation Mapping (Current)

- `REFL` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `ASSUME` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `TRANS` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `MK_COMB` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `ABS` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `BETA` -> `src/kernel/thm.mbt` (implemented; De Bruijn beta core + boundary lift).
- `EQ_MP` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `DEDUCT_ANTISYM_RULE` -> `src/kernel/thm.mbt` (implemented; De Bruijn core + boundary lift).
- `INST_TYPE` -> `src/kernel/thm.mbt` (implemented; De Bruijn substitution core + boundary lift).
- `INST` -> `src/kernel/thm.mbt` (implemented; De Bruijn substitution core + boundary lift).

== Design Delta vs HOL Light

QED and HOL Light share the LCF principle and primitive-rule trust model, but QED currently differs in two engineering choices:

1. Rule execution layer:
  HOL Light executes directly over named terms; QED executes rule cores over De Bruijn objects and lifts results to named boundaries.
2. Constant signature policy:
  HOL Light uses globally unique constant naming; QED currently uses scoped signature stacks with explicit shadowing.

These deltas are intentional and must be read as implementation-level policy choices, not changes to the object-logic proposition/equality calculus.

#keyblock("warning", [Error Semantics Status], [
  Full kernel-wide structured error propagation is still in migration. Current interfaces mix option-style failures with typed error returns in selected modules.
])

== Target Error Taxonomy (`LogicError`)

The target kernel-facing error type is:

$
  "LogicError" ::= & "TypeMismatch"         && " typing mismatch" \
                 | & "VariableCaptured"     && " capture risk" \
                 | & "NotAnEquality"        && " equality shape required" \
                 | & "NotBoolTerm"          && " boolean proposition required" \
                 | & "AlphaMismatch"        && " alpha check failed" \
                 | & "InvalidInstantiation" && " ill-formed substitution" \
                 | & "VarFreeInHyp"         && " binder free in assumptions" \
                 | & "NotTrivialBetaRedex"  && " invalid beta-redex shape" \
                 | & "BoundaryFailure"      && " named/db conversion failed"
$

Intended alignment with rule-level failure clauses:

- `REFL`: malformed term or equality formation failure -> `BoundaryFailure` or `TypeMismatch`.
- `ASSUME`: non-boolean proposition -> `NotBoolTerm`.
- `TRANS`: non-equality premise -> `NotAnEquality`; middle mismatch -> `AlphaMismatch`; chain typing failure -> `TypeMismatch`.
- `MK_COMB`: non-equality premise -> `NotAnEquality`; function or argument typing mismatch -> `TypeMismatch`.
- `ABS`: non-variable binder -> `InvalidInstantiation`; binder free in assumptions -> `VarFreeInHyp`.
- `BETA`: non-redex input -> `NotTrivialBetaRedex`; redex typing failure -> `TypeMismatch`.
- `EQ_MP`: equality premise malformed -> `NotAnEquality`; lhs/premise mismatch -> `AlphaMismatch`; non-boolean proposition -> `NotBoolTerm`.
- `DEDUCT_ANTISYM_RULE`: set-removal target mismatch -> `AlphaMismatch`; non-propositional premise -> `NotBoolTerm`.
- `INST_TYPE` and `INST`: invalid substitution shape -> `InvalidInstantiation`; capture-risk boundary -> `VariableCaptured`; post-substitution typing failure -> `TypeMismatch`.

This mapping is normative for the final migrated API and gives a direct bridge from prose failure clauses to machine-checkable error constructors.

= Documentation Roadmap

This document is a living formal artifact. The target final version includes:

1. full rule-by-rule formalization of all primitive inference rules,
2. explicit substitution lemmas and alpha-equivalence lemmas,
3. a consistency assumptions section,
4. an interface theorem connecting kernel and tactic layers,
5. a revision log linking formal clauses to commit history.

#keyblock("info", [Current Status], [
  This revision establishes the minimum logical closure needed for soundness auditing: reserved equality discipline, two-layer judgments, alpha-quotient assumptions, boundary denotation bridges, definitional conservativity gates, and admissible type-extension/state-history constraints.
])

= Appendix A: Primitive Rule Dependency Matrix

Each primitive rule is required to reference the following dependency blocks.

- `REFL` -> core typing of input term; reserved equality formation; theorem boundary constructor.
- `ASSUME` -> boolean typing in resolved layer; alpha-quotient insertion law.
- `TRANS` -> equality destructor/constructor typing; alpha-aware middle-term matching; typed De Bruijn core matching (binder-domain labels preserved); assumption union laws.
- `MK_COMB` -> function application typing; equality formation at codomain; assumption union laws.
- `ABS` -> binder well-formedness; free-variable side condition over assumption quotient; equality congruence under abstraction.
- `BETA` -> typed De Bruijn redex shape (`DAbs(tau, ...)`); binder/argument type agreement; well-scoped substitution lemmas; boundary lift stability.
- `EQ_MP` -> boolean equality premise typing; alpha-aware premise matching; assumption union laws.
- `DEDUCT_ANTISYM_RULE` -> quotient removal law; proposition typing for both conclusions; equality formation.
- `INST_TYPE` -> well-formed type substitution; typing preservation under type substitution; theorem-structure preservation; definitional-instantiation coherence under `DefOK`; non-empty type admissibility under `TypeDefOK`; constant principal-schema instance preservation (`≼`).
- `INST` -> parallel capture-avoiding substitution; domain key well-formedness; typing preservation under term substitution.

Acceptance condition for this matrix:

- every side condition in each rule schema points to one of the dependency blocks above;
- no side condition remains as an unbound prose-only requirement.

= Appendix B: P0 Closure Checklist

Checklist for minimal audit-ready closure:

1. Reserved logical equality symbol defined and non-shadowable.
2. Named elaboration and resolved core typing formally separated.
3. Scope-mutation stability theorem stated over resolved terms.
4. Assumption sets defined as finite alpha-quotient sets.
5. Boundary conversion includes denotation-preserving lemmas.
6. Rule lifting theorem upgraded from structural to semantic preservation.
7. Definitional extension side conditions include type-variable closure ($"TVars"(r) ⊆ "TVars"(tau)$).
8. `DefOK` admissibility judgment and global admissibility envelope are stated and referenced.
9. Primitive-rule dependency matrix completed (10/10 coverage).
10. Soundness dependency graph present and cited by soundness obligations.
11. Failure clauses remain aligned with rule side conditions after closure edits.
12. Type-constructor extensions are gated by `TypeDefOK` with non-empty witness discipline.
13. Global theory history (`DefHeads`) is separated from local poppable scope and is monotone.
14. De Bruijn core matching is type-sensitive (no binder-domain type erasure during boundary lowering).
15. Constant typing uses principal schema + instance relation (`tau ≼ tau_gen`) so polymorphic constants remain usable at admissible instances.
16. Primitive choice operator (`@`) and its axiom schema are explicitly stated in foundations.
17. `SpecOK` is documented as a derived admission rule (Choice + `DefOK`), not a standalone primitive rule.
18. Infinity-anchor theorem identifier (`IND_INFINITY_AXIOM`) is explicitly fixed.

This checklist is intended to be consumed before implementation alignment work starts.

= Appendix C: Definition and State Soundness Audit Scenarios

Audit scenarios focused on definition-layer completeness:

1. *Ghost-Type Rejection Scenario*:
  attempt $"def" c : "bool" = r(alpha)$ with $alpha ∉ "TVars"("bool")$;
  expected result: rejected by `TVars(r) ⊆ TVars(tau)`.
2. *Instantiation Coherence Scenario*:
  from an admissible definition theorem $tack.r c = r$, apply $"INST_TYPE"$ on head variables;
  expected result: instantiated head/body remain coherent as one definitional instance.
3. *Shadowing Separation Scenario*:
  local scope shadowing of ordinary constants is permitted;
  definitional head reuse is rejected by global freshness in $"DefOK"$.
4. *Old-Language Conservativity Scenario*:
  after admissible extension, any theorem not mentioning the new symbol is derivable iff it was derivable before.
5. *Pop-Then-Redefine Rejection Scenario*:
  define head $c$, pop local scope, attempt defining $c$ again;
  expected result: rejected because $c in "DefHeads"(T)$ despite local lookup removal.

Passing all five scenarios is required before claiming definition/state-layer soundness closure.

= Appendix D: Type Soundness Audit Scenarios

Audit scenarios focused on type-extension completeness:

1. *Empty-Type Constructor Rejection Scenario*:
  propose a new type constructor without witness theorem;
  expected result: rejected by $"TypeDefOK"$ admissibility gate.
2. *Witness-Carrying Type Definition Scenario*:
  introduce a type constructor with a valid non-emptiness witness;
  expected result: accepted and preserves global non-empty-type invariant.
3. *INST_TYPE Inhabitation Scenario*:
  apply $"INST_TYPE"$ after admissible type extensions;
  expected result: substitutions range over inhabited types only.
4. *No Semantic Escape Scenario*:
  attempt to derive a theorem relying on empty-carrier semantics;
  expected result: blocked because no empty type can be introduced admissibly.
5. *Polymorphic Constant Instantiation Scenario*:
  define $id$ at principal schema $"fun"(alpha, alpha)$, then use it at $"fun"("bool", "bool")$ and $"fun"("int", "int")$;
  expected result: both uses are accepted via the instance relation $tau ≼ tau_"gen"$, without requiring per-type renamed constants.

Passing all five scenarios is required before claiming type-layer soundness closure.

= Appendix E: Typed De Bruijn Core Audit Scenarios

Audit scenarios focused on typed-core/boundary consistency:

1. *Binder-Type Distinction Scenario*:
  compare $lambda (x:tau_1). x$ and $lambda (x:tau_2). x$ with $tau_1 != tau_2$;
  expected result: lowered typed De Bruijn abstractions are distinct ($"DAbs"(tau_1, ...) != "DAbs"(tau_2, ...)$).
2. *TRANS Middle-Term Guard Scenario*:
  chain two equalities whose middle terms are structurally similar but differ in binder-domain type labels;
  expected result: TRANS rejects by typed-core mismatch.
3. *BETA Binder Agreement Scenario*:
  attempt beta contraction with argument type not equal to abstraction binder-domain label;
  expected result: rejected before contraction.
4. *Boundary Lift Type Coherence Scenario*:
  lower and lift a theorem involving typed abstractions;
  expected result: reconstructed theorem preserves abstraction-domain types and cannot cross-type-identify abstractions.

Passing all four scenarios is required before claiming De Bruijn core/type-system coherence closure.

= Appendix F: Specification and Choice Audit Scenarios

Audit scenarios focused on derived specification admission discipline:

1. *Empty-Hypothesis Witness Requirement Scenario*:
  provide a witness theorem with non-empty assumptions for specification introduction;
  expected result: rejected by `SpecOK` witness-shape policy.
2. *Freshness Collision Scenario*:
  attempt to introduce specification constant $c$ where $c$ is reserved or already present in theory history;
  expected result: rejected by specification freshness constraints.
3. *Type-Schema Widening Scenario*:
  attempt specification admission where implementation widens schema beyond $"Gen"(tau)$;
  expected result: rejected by strict type-schema lock.
4. *Derived-Path Integrity Scenario*:
  attempt to admit specification constant without explicit Choice + `DefOK` derivation trace;
  expected result: rejected because `SpecOK` is derived-only in this stage.
5. *Old-Language Conservativity Scenario*:
  after admissible specification extension, prove a sentence not mentioning the new symbol;
  expected result: derivable iff derivable before extension.

Passing all five scenarios is required before claiming specification-layer closure.
