#set page(paper: "a4", margin: (x: 2.3cm, y: 2.0cm))
#set text(size: 10.5pt)
#set par(leading: 0.65em)
#set heading(numbering: "1.")

#align(center)[
  #text(size: 19pt, weight: "bold")[QED Typed HOL Core]
  #linebreak()
  #text(size: 12pt)[A Mathematical Specification and Proof Guide]
  #linebreak()
  #text(size: 9pt, fill: gray)[Version 1.0 · 2026-10-12]
]

#v(1em)

= Abstract

QED's formal logic is a simply typed higher-order logic with polymorphic constant
schemas, equality, and Hilbert choice. This document specifies the logic from
typed syntax through semantics and primitive derivation rules. The syntax is
intrinsically typed: a malformed application, abstraction, or rule instance
cannot be constructed as a term or derivation.

The Lean 4 development in `formal_verification/QEDFV/HOL` is the machine-checked
definition of this mathematical core. Its public theorem
`QEDFV.HOL.typed_hol_proof_complete` packages the current results: evaluation
commutes with renaming and substitution, beta reduction is semantically valid,
typed derivations are sound, the extension contracts have their stated semantic
properties, and a concrete interpretation rules out derivation of a false
sentence. The proof has no project-defined axioms or unfinished proof holes.
Lean reports dependencies on `propext`, `Classical.choice`, and `Quot.sound`.

The development proves the logic described here. It does not prove that the
separate MoonBit implementation refines this Lean calculus. That boundary is
part of the specification status, not an implicit premise of soundness.

= Scope and status

== Normative mathematical core

The normative core consists of the typed calculus, its semantics, and the
explicitly scoped metatheorems below. The matching
Lean declarations are the authoritative formal definitions and checked theorems.
If prose and Lean disagree, the discrepancy must be resolved by correcting the
specification or the formalization; implementation tests cannot silently change
the calculus.

This specification fixes:

- simple types, typed terms, contexts, sequents, and substitutions;
- the ten primitive derivation constructors;
- the set-theoretic interpretation and validity relation;
- soundness and the semantic extension results proved in Lean;
- the exact limits of those results.

== Implementation boundary

QED's intended architecture has a small theorem-producing kernel. Parsers,
elaborators, tactics, automation, and user interfaces may propose proof steps,
but a result is trusted only when checked by the kernel.

The Typed HOL proof is a proof about the Lean calculus. It does not include a
verified translation from MoonBit terms, theorem objects, mutable signature
state, or primitive-rule code into this calculus. It also does not prove
completeness, syntactic derivability preservation for extensions, or correctness
of user-facing proof search. Those claims require separate formal results.

= Design at a glance

The theory has four layers:

#enum(
  [*Typed language.* Types determine the carrier of every term. Bound variables
  use De Bruijn indices, and constant occurrences carry an explicit type
  substitution.],
  [*Proof calculus.* A derivation is an inductive object indexed by its sequent.
  The index rules out ill-typed rule applications before soundness is considered.],
  [*Semantics.* Types denote nonempty carriers, terms denote carrier elements,
  and sequents are valid when true assumptions imply a true conclusion in every
  environment.],
  [*Metatheory.* Each primitive constructor preserves validity. Induction over a
  derivation proves soundness without placing a soundness law inside a model.]
)

The dependency order is:

#align(center)[
  #text(weight: "bold")[
    typed syntax -> evaluation laws -> primitive-rule preservation ->
    derivation soundness -> extension and consistency results
  ]
]

No theorem in this chain is used as a premise for its own semantic model.

= Types and signatures

== Types

Type-variable identifiers are natural numbers. The type grammar is:

```text
Ty ::= bool | ind | var(i) | arr(Ty, Ty)
```

Lean names these constructors `Ty.bool`, `Ty.ind`, `Ty.var i`, and `Ty.arr a b`.
The type `bool` denotes propositions, `ind` denotes individuals, and `arr a b`
denotes functions from `a` to `b`.

A type substitution is a total map `theta : Nat -> Ty`. It acts structurally:

```text
bool[theta]       = bool
ind[theta]        = ind
var(i)[theta]     = theta(i)
arr(a, b)[theta]  = arr(a[theta], b[theta])
```

A signature is a total map `S : Nat -> Ty`. Its value is a principal constant
schema. A constant occurrence `const(c, theta)` has type `S(c)[theta]`.
Polymorphism is therefore schema instantiation, not an untyped escape hatch.

== Type valuations and non-emptiness

A type valuation is `rho : Nat -> Type` (the carrier universe used by this Lean development). It is admissible when every variable
carrier is inhabited:

```text
Admissible(rho) := forall i, Nonempty (rho i)
```

The type interpretation is:

```text
denote(bool, rho)       = Prop
denote(ind, rho)        = Nat
denote(var(i), rho)     = rho(i)
denote(arr(a, b), rho)  = denote(a, rho) -> denote(b, rho)
```

Every type has a nonempty denotation under an admissible valuation. For an arrow
type, a constant function returning an inhabitant of the codomain is enough.
`Ty.carrier_nonempty` proves this by induction; non-emptiness is established,
not assumed as a model law.

= Contexts and terms

== Typed contexts

A context is a finite list of types. The variable at index zero has the first
type in the list, and `succ` moves to an outer binding:

```text
Var(a :: Gamma, a)
Var(Gamma, a) -> Var(b :: Gamma, a)
```

This is De Bruijn syntax. Variable names and alpha-equivalence are not part of
the core language.

== Term grammar and typing

Terms are indexed by both a signature/context and their result type:

```text
var(v)       : Term(S, Gamma, a)                 when v : Var(Gamma, a)
const(c, th) : Term(S, Gamma, S(c)[th])
app(f, x)    : Term(S, Gamma, b)                 when f : Term(S, Gamma, arr(a,b))
                                                   and x : Term(S, Gamma, a)
lam(body)    : Term(S, Gamma, arr(a,b))          when body : Term(S, a :: Gamma, b)
eq           : Term(S, Gamma, arr(a, arr(a, bool)))
choice       : Term(S, Gamma, arr(arr(a, bool), a))
```

There is no untyped application followed by a repair judgment. The type indices
make domain mismatches unrepresentable. Constants and bound variables have
distinct constructors.

== Notation for reading the calculus

In mathematical notation, $Gamma tack.r t : a$ means that `t` inhabits
`Term S Gamma a`; it abbreviates an indexed term, rather than a separate
algorithm for checking an untyped expression. We write $lambda x:a. t$ for
`lam(t)`, $t u$ for `app(t,u)`, and $s =_a t$ for applying the intrinsic
equality constructor at type `a` to `s` and `t`. Binder names in this notation
are for the reader; the stored variables are De Bruijn indices.

For example, in context `Gamma = [a]` with outer variable `y`, the named
expression `(lambda x:a. lambda z:a. x) y` reduces to `lambda z:a. y`. Its
De Bruijn body is `lam(var(succ(zero)))`; substituting `y` shifts it past
`z`, producing `lam(var(succ(zero)))` in the target context. The surviving
outer variable remains outer, rather than being captured as `z`.

== Renaming, substitution, and type instantiation

A renaming `r : Ren Gamma Delta` maps each variable to a variable of the same
type. `Ren.lift` preserves the new zero variable and shifts outer variables.

A term substitution `sigma : Sub S Gamma Delta` maps each variable to a term of
the same type. `Sub.lift` leaves the new zero variable unchanged and renames
the substituted outer terms. Capture avoidance is structural.

The operations `Term.rename`, `Term.substitute`, and `Term.instType` recurse
over the typed term. The Lean proofs establish evaluation commutation for
renaming and substitution, the beta evaluation equation, and evaluation
coherence for type instantiation, including terms below binders.

= Sequents and primitive derivations

== Sequent judgment

For a signature `S` and context `Gamma`, a sequent contains a list of boolean
assumptions and a boolean conclusion:

```text
Sequent S Gamma := { hyps : List (Term S Gamma bool),
                     concl : Term S Gamma bool }
```

`Derivation S s` is an inductive proposition indexed by the complete sequent
`s`. A constructor can produce only the exact assumptions and conclusion in its
type.

== Primitive rules

The calculus has ten primitive constructors. In each rule, all displayed terms
share the signature `S`; premises and conclusions share the stated context except
for binder introduction and instantiation. `A` and `B` below denote assumption
lists, `++` is list concatenation (the Lean helper `union`), and an empty list is
omitted to the left of `|-`. Assumption order and duplicates remain in the
syntax; validity requires each listed assumption to hold.

There is no primitive choice axiom, defining-equation admission rule, or
type-definition admission rule in `Derivation`. Choice is interpreted by the
selector below; the extension results concern semantic validity separately.

=== Equality rules

```text
REFL:
  |- t = t

ASSUME:
  [p] |- p

TRANS:
  A |- s = t       B |- t = u
  -----------------------------
       A ++ B |- s = u

MK_COMB:
  A |- f = g       B |- x = y
  -----------------------------
       A ++ B |- f x = g y
```

`MK_COMB` requires `f` and `g` to have type `a -> b`, and `x` and `y`
to have type `a`; the indices enforce these requirements.

=== Abstraction and computation

```text
ABS:
  weaken(A) |- s = t
  -----------------------------
  A |- (lam s) = (lam t)

BETA:
  |- (lam s) x = s.substitute (Sub.single x)
```

`weaken` shifts each assumption past the new binder. The typed context form
expresses the usual freshness condition. `BETA` uses the capture-avoiding
substitution for the zero-index variable.

=== Propositional equality rules

```text
EQ_MP:
  A |- p = q       B |- p
  -------------------------
       A ++ B |- q

DEDUCT:
  A |- p           B |- q
  -----------------------------------------------
  (remove A q) ++ (remove B p) |- p = q
```

`remove` deletes every occurrence of the displayed assumption. `DEDUCT` has no
additional union-equality side condition: its soundness follows from boolean
equality semantics and the two premise-validity proofs.

=== Instantiation rules

```text
INST_TERM:
  A |- p
  ----------------
  termSubst(sigma, A) |- p[sigma]

INST_TYPE:
  A |- p
  ----------------
  typeSubst(theta, A) |- p[theta]
```

`INST_TYPE` maps contexts and constant occurrences with the same schema
substitution. These are typed constructors, not post-hoc checks.

= Semantics

== Environments and interpretations

For admissible `rho`, an environment supplies a value of the corresponding
denoted type to every variable:

```text
Env rho Gamma := forall a, Var(Gamma, a) -> denote(a, rho)
```

An environment extension adds the value for the new zero-index variable. A
constant interpretation has type:

```text
ConstVal S := forall rho, Admissible(rho) -> forall c, denote(S(c), rho)
```

A constant occurrence at schema instance `theta` is evaluated using the type
valuation induced by `theta`:

```text
(theta.pull rho)(i) = denote(theta(i), rho)
denote(a[theta], rho) = denote(a, theta.pull rho)
```

The second equality (`Ty.denote_subst`) transports the constant value into the
carrier indexed by its instantiated type. This transport is part of evaluation,
not a model law supplied by a caller.

== Term evaluation

Write `E(t)` for evaluation at `I, rho, h_rho, eta`. Evaluation is the following
recursive function; the constant case uses the type transport just described.

```text
E(var(v))       = eta(v)
E(const(c, th)) = transport(I(th.pull rho, th.pull_admissible h_rho, c))
E(app(f, x))    = E(f)(E(x))
E(lam(t))       = fun x => eval(t, I, rho, h_rho, eta.extend x)
E(eq)           = fun x y => x = y
E(choice[a])    = select(denote(a, rho))
```

In particular, equality at `bool` is equality of Lean propositions.
Propositional extensionality relates this equality to logical equivalence, and
function extensionality validates the abstraction rule.

`select` returns an element satisfying a predicate whenever that predicate has a
witness. `select_natural` proves the required coherence under type
instantiation. Choice coherence is therefore a theorem about the selector, not
a soundness field assumed in a model.

== Validity

For a fixed constant interpretation `I`, a sequent is valid when every admissible
valuation and environment satisfying its assumptions also satisfies its conclusion:

```text
Valid I s := forall rho h_rho eta,
  (forall h, h in s.hyps -> eval(h, I, rho, eta)) ->
  eval(s.concl, I, rho, eta)
```

The definition covers open contexts as well as closed terms.

= Main metatheorems

== Evaluation laws

The Lean development proves by structural induction:

- renaming commutes with evaluation;
- substitution commutes with evaluation;
- beta evaluation equals evaluation of the capture-avoiding substitution;
- type instantiation commutes with evaluation, including choice.

The substitution law is:

```text
eval(t[sigma], eta) = eval(t, eta_sigma)
eta_sigma(v) = eval(sigma(v), eta)
```

Under type instantiation, evaluation at `rho` corresponds to evaluation of the
original term at `theta.pull rho`, with the environment pulled back as well.
The Lean statement uses `HEq` because the two carrier expressions have different
type indices before transport. These lemmas are the semantic basis of the rule
proof; they do not assume soundness of the derivation relation.

== Rule preservation and derivation soundness

Each primitive rule preserves validity. The theorem `derivation_sound` proceeds
by induction on `Derivation`, with one case per constructor:

```text
Derivation S s -> forall I, Valid I s
```

For example, `TRANS` receives validity of `A |- s = t` and `B |- t = u`.
An environment satisfying `A ++ B` satisfies both lists, so the induction
hypotheses give `eval(s) = eval(t)` and `eval(t) = eval(u)`. Equality
transitivity yields the conclusion. `INST_TERM` uses the substitution law to
turn a target environment into the premise environment; `INST_TYPE` uses type
transport and `select_natural`. Thus neither case postulates the desired rule
soundness in the interpretation.

The canonical interpretation `canonicalConstVal` chooses an inhabitant for every
constant carrier, producing a model for every signature. `TypedHOLModel` packages
an interpretation with the proved `ChoiceNatural` property used by the
type-instantiation case.

== Non-triviality witness

For `standardSignature`, `ind` is interpreted as `Nat`, constant 0 as zero,
and constant 1 as successor. The closed sentence `succ(0) = 0` evaluates to
`False`. By derivation soundness it is not derivable. This is a concrete
non-triviality witness for the calculus.

= Conservative semantic extensions

The Lean core defines semantic extension contracts over one fixed signature.
These contracts prove validity results. They are not derivation-erasure theorems.

== Definitions

`DefinitionGate` contains a fresh identifier `c`, a closed right-hand side
`rhs : Term S [] (S c)`, and `typeVars(rhs) subset typeVars(S c)`. Freshness
means that `c` does not occur in `rhs`. Since `S` is total, `c` already has a
schema slot. The gate overrides that slot pointwise; it does not allocate an
identifier or prove that `c` was unused throughout a global declaration history.

The extended interpretation assigns `c` the value of `rhs` in the old
interpretation and leaves every other constant unchanged. Lean proves:

- the defining equation `c = rhs` is valid in the extended interpretation;
- a sequent not containing `c` is valid before and after the interpretation
  change in both directions.

== Specifications

`SpecificationGate` contains a fresh identifier `c`, a type `a`, a predicate
`predicate : Term S [a] bool`, a closed witness `w : Term S [] a`, and the
conditions `c` absent from both predicate and witness, and
`typeVars(predicate) subset typeVars(a)`. Its interpretation also requires
`S(c) = a`. There is no additional type-variable closure field for the witness
in the current gate.

The body `predicate(w)` is the witness obligation. Given a typed derivation of
that body, the extended interpretation assigns `c` the selected value satisfying
the predicate. Lean proves the resulting predicate theorem and old-language
validity equivalence.

== Type-definition contracts

`PredicateFamily` gives a representation type, a predicate on its carrier under
each admissible valuation, and a witness for every valuation. The corresponding
new carrier is the subtype of values satisfying that predicate. Lean proves:

- the subtype carrier is nonempty;
- `abs(rep(x)) = x` for subtype values;
- `rep(abs(x)) = x` when the predicate holds;
- `pred(rep(x))` for every subtype value `x`.

This is the carrier-level mathematics of a witnessed type definition. The current
`Extension.typeDefinition` constructor preserves the constant interpretation; it
does not allocate a new type-constructor signature. No stronger claim is made.

== Finite extension sequences

A finite list of extensions is interpreted as a sequence of semantic
interpretation changes. If a sequent contains none of the fresh identifiers
introduced by the sequence, Lean proves:

```text
Valid I_extended s <-> Valid I_base s
```

The freshness checks are local to each gate. A sequence does not check globally
distinct identifiers or protect earlier gate equations against later overrides.
For instance, two definitions of the same `c` with different right-hand sides
can each satisfy their local gate; the second override need not preserve the
first equation. Model non-emptiness here means an interpretation of the fixed
signature exists, not that all declaration equations in an arbitrary sequence
hold simultaneously.

This is semantic validity conservativity. It does not translate an extended
derivation into a base derivation, and no completeness theorem is used to infer
such a translation.

= Proof dependency and trust basis

The proof dependency is one-way:

#enum(
  [typed terms and types],
  [evaluation and substitution lemmas],
  [validity preservation for each primitive rule],
  [induction on typed derivations],
  [extension validity and concrete non-triviality results]
)

The public package theorem is `QEDFV.HOL.typed_hol_proof_complete`.

#table(
  columns: (1.35fr, 2.45fr),
  [*Topic*], [*Lean source*],
  [Types and carrier non-emptiness], [QEDFV/HOL/Types.lean],
  [Typed terms and substitutions], [QEDFV/HOL/Terms.lean],
  [Evaluation and beta], [QEDFV/HOL/Evaluation.lean],
  [Type-instantiation coherence], [QEDFV/HOL/Instantiation.lean],
  [Primitive validity rules], [QEDFV/HOL/Rules.lean],
  [Inductive derivation soundness], [QEDFV/HOL/Derivation.lean],
  [Definitions and transport], [QEDFV/HOL/Definitions.lean, Transport.lean],
  [Specification and typedef], [QEDFV/HOL/Specification.lean, TypeDefinitions.lean],
  [Finite semantic conservativity], [QEDFV/HOL/Conservativity.lean],
  [Concrete model and public package], [QEDFV/HOL/Concrete.lean, Soundness.lean],
)

`lake build` checks the complete QEDFV library. The audited `#print axioms`
results for the public package, soundness theorem, semantic conservativity
theorem, and concrete non-derivability theorem are `propext`, `Classical.choice`,
and `Quot.sound`. These are Lean/mathlib foundational dependencies; the project
adds no custom axiom to assert soundness.

= Claims and exact limits

The current formal result supports:

- validity of every `Derivation` in every interpretation of its signature;
- nonempty carriers under admissible type valuations;
- the stated definition and specification semantic contracts;
- the witnessed predicate-subtype carrier laws;
- old-language validity invariance under finite modeled extensions;
- non-derivability of the concrete false sentence.

The current formal result does not establish:

- completeness of the typed calculus;
- syntactic conservativity by translating extended derivations;
- a formal mapping from MoonBit kernel operations or theorem objects to Lean
  `Derivation`;
- correctness of parsing, elaboration, tactics, theorem replay, or user scripts;
- correctness of mutable signature history, identity allocation, or provenance in
  the MoonBit implementation;
- a new type-constructor signature extension from `TypeDefContract` alone;
- joint satisfaction of all gate equations under unrestricted later overrides.

Implementation integration must enforce compatible declaration history and
theorem provenance. The open sibling-state theorem-reuse defect (issue #15)
is an implementation risk outside this Lean calculus; these proofs do not
resolve or certify that behavior.

These distinctions are essential when reading `lake build`: it checks the stated
typed theory and its theorems. It does not verify a separate program.

= Maintenance rule

Changes to types, term constructors, primitive rules, or extension semantics must
update the Lean definitions, this document, and the proof-status record together.
A new rule or extension is part of the trusted mathematical core only after its
typed constructor, semantic preservation argument, and integration into
`derivation_sound` are checked.

An implementation may optimize representation or proof search only when it
preserves this calculus. Until a checked refinement establishes that
correspondence, implementation behavior and Typed HOL theorems must be reported
as separate evidence.
