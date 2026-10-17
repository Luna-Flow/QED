// ============================================================================
//  QED formal specification — document style
//  One visual system: a thin coloured bar on the left marks every kind of
//  annotated block (the Lean 4 annotations set the pattern).
// ============================================================================
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// ---- palette ---------------------------------------------------------------
#let ink = rgb("#1b1f2a")
#let muted = rgb("#5f6675")
#let hairline = rgb("#cfd4dd")
#let c-lean = rgb("#1d4ed8")       // Lean 4 annotations (unchanged)
#let c-def = rgb("#0f766e")        // definitions
#let c-thm = rgb("#4c3fa3")        // propositions, lemmas, theorems, corollaries
#let c-contract = rgb("#a16207")   // implementation contracts and obligations
#let c-proof = rgb("#8a92a3")      // proofs
#let c-note = rgb("#5f6675")       // remarks and examples

#let info-color = rgb("#475569")
#let warning-color = rgb("#a16207")
#let critical-color = rgb("#b91c1c")

#let level-color(level) = {
  if level == "info" { info-color } else if level == "warning" { warning-color } else { critical-color }
}

// ---- running section title (header) ------------------------------------------
#let current-section() = context {
  let before = query(heading.where(level: 1).before(here()))
  if before.len() > 0 { before.last().body }
}

// ---- page and text ---------------------------------------------------------
#set document(
  title: "A Formal Mathematical Specification for QED",
  author: "Luna-Flow",
)
#set page(
  paper: "a4",
  margin: (x: 2.5cm, top: 2.7cm, bottom: 2.5cm),
  header: context {
    if counter(page).get().first() > 1 {
      set text(size: 8.5pt, fill: muted)
      grid(
        columns: (1fr, auto),
        [QED — A Formal Mathematical Specification], current-section(),
      )
      v(-5pt)
      line(length: 100%, stroke: 0.4pt + hairline)
    }
  },
  footer: context {
    set text(size: 8.5pt, fill: muted)
    align(center, counter(page).display("1"))
  },
)
#set text(font: "New Computer Modern", size: 10.5pt, lang: "en", fill: ink)
#set par(justify: true, leading: 0.66em, spacing: 0.95em)
#set math.equation(numbering: none)
#set list(indent: 0.6em, body-indent: 0.5em)
#set enum(indent: 0.6em, body-indent: 0.5em)
#set outline(indent: auto)
#set table(
  stroke: (_, y) => (
    top: if y <= 1 { 0.6pt + ink } else { 0.3pt + hairline },
  ),
  fill: (_, y) => if y == 0 { luma(246) },
  inset: (x: 7pt, y: 5pt),
)

#show link: set text(fill: c-lean)
#show raw: set text(font: "DejaVu Sans Mono", size: 0.86em)
#show raw.where(block: false): it => box(
  fill: luma(244),
  inset: (x: 2.5pt),
  outset: (y: 2.5pt),
  radius: 2pt,
  it,
)

// ---- headings --------------------------------------------------------------
#let env-counter = counter("env")

#show heading.where(level: 1): it => {
  env-counter.update(0)
  v(1.7em, weak: true)
  block(width: 100%, sticky: true, below: 1.1em)[
    #set text(size: 15pt, weight: "bold")
    #if it.numbering != none {
      text(fill: c-lean)[#counter(heading).display(it.numbering)]
      h(9pt)
    }
    #it.body
    #v(-1pt)
    #line(length: 100%, stroke: 0.7pt + hairline)
  ]
}
#show heading.where(level: 2): it => {
  v(1.2em, weak: true)
  block(sticky: true, below: 0.75em)[
    #set text(size: 11.5pt, weight: "bold")
    #if it.numbering != none {
      text(fill: c-lean)[#counter(heading).display(it.numbering)]
      h(7pt)
    }
    #it.body
  ]
}
#show heading.where(level: 3): it => {
  v(1em, weak: true)
  block(sticky: true, below: 0.6em)[
    #set text(size: 10.5pt, weight: "bold", style: "italic")
    #it.body
  ]
}

// ---- annotated blocks --------------------------------------------------------
// Number of an environment: <section>.<index within the section>.
#let env-number() = context {
  let section = counter(heading).get().at(0, default: 0)
  [#section.#env-counter.get().first()]
}

#let env-block(color, label, title, body, numbered: true, tint: false) = {
  if numbered { env-counter.step() }
  block(
    width: 100%,
    above: 1.05em,
    below: 1.05em,
    inset: if tint { (left: 11pt, right: 10pt, y: 8pt) } else { (left: 11pt, y: 2pt) },
    stroke: (left: 1.6pt + color),
    fill: if tint { color.lighten(95%) },
    radius: if tint { (right: 3pt) } else { 0pt },
    {
      text(weight: "bold", fill: color)[#label#if numbered [ #env-number()]]
      if title != none { text(weight: "bold")[ (#title)] }
      text(weight: "bold", fill: color)[.]
      [ ]
      body
    },
  )
}

#let definition(title, body) = env-block(c-def, [Definition], title, body)
#let proposition(title, body) = env-block(c-thm, [Proposition], title, body, tint: true)
#let lemma(title, body) = env-block(c-thm, [Lemma], title, body, tint: true)
#let theorem(title, body) = env-block(c-thm, [Theorem], title, body, tint: true)
#let corollary(title, body) = env-block(c-thm, [Corollary], title, body, tint: true)
#let property(title, body) = env-block(c-thm, [Property], title, body, tint: true)
#let example(title, body) = env-block(c-note, [Example], title, body)
#let remark(title, body) = env-block(c-note, [Remark], title, body, numbered: false)
#let note(label, body) = env-block(c-note, label, none, body, numbered: false)
#let contract(label, body) = env-block(c-contract, label, none, body, numbered: false)

#let proof(title, body) = block(
  width: 100%,
  above: 0.9em,
  below: 1.05em,
  inset: (left: 11pt, y: 1pt),
  stroke: (left: 0.9pt + c-proof),
  {
    text(style: "italic", weight: "bold", fill: muted)[Proof#if title != none [ #title].]
    [ ]
    body
    h(1fr)
    text(fill: muted)[∎]
  },
)

// Callouts: reading guide, scope statements, integrity conditions.
#let keyblock(level, title, body) = {
  let color = level-color(level)
  block(
    width: 100%,
    above: 1.1em,
    below: 1.1em,
    inset: (left: 13pt, right: 12pt, y: 9pt),
    stroke: (left: 2.6pt + color),
    fill: color.lighten(94%),
    radius: (right: 3pt),
    {
      text(size: 8.6pt, weight: "bold", fill: color, tracking: 0.05em)[#upper(title)]
      v(0.3em)
      body
    },
  )
}

// Lean 4 annotations (blue bar): the pattern the other blocks follow.
#let lean-note(label, module, names) = block(
  width: 100%,
  above: 0.9em,
  below: 0.9em,
  breakable: false,
  inset: (left: 10pt, y: 1pt),
  stroke: (left: 1.6pt + c-lean),
  {
    set text(size: 9pt)
    set par(justify: false)
    text(fill: c-lean, weight: "bold")[#label]
    [ ]
    text(fill: muted)[#raw("formal_verification/QEDFV/HOL/" + module + ".lean")]
    [: ]
    names.map(n => raw(n)).join([; ])
    [.]
  },
)
#let lean-proof(module, names) = lean-note([Lean 4 proof.], module, names)
#let lean-def(module, names) = lean-note([Lean 4 definition.], module, names)

// ---- title -------------------------------------------------------------------
#v(0.6em)
#align(center)[
  #set par(justify: false)
  #text(size: 20pt, weight: "bold")[A Formal Mathematical Specification \ for QED]
  #v(0.4em)
  #text(size: 12.5pt, fill: muted)[A Minimal LCF-Style HOL Kernel in MoonBit]
]
#v(0.9em)
#block(
  width: 100%,
  stroke: (top: 1pt + ink, bottom: 0.4pt + hairline),
  inset: (y: 8pt),
  {
    set text(size: 9pt)
    set par(justify: false)
    grid(
      columns: (auto, 1fr),
      column-gutter: 14pt,
      row-gutter: 5pt,
      text(fill: muted, weight: "bold")[Project], [Luna-Flow/QED],
      text(fill: muted, weight: "bold")[Formal development],
      [Lean 4 development in #raw("formal_verification/QEDFV/HOL")],
      text(fill: muted, weight: "bold")[Related documents],
      [Proof plan and branch contract in #raw("formal_verification/"); current status and revision context in #raw("doc/manual/conformance.md")],
    )
  },
)
#v(0.8em)

= Abstract

QED is a theorem prover built around a small LCF-style kernel. Its mathematical
core is a simply typed higher-order language with polymorphic constant schemas,
equality, and Hilbert choice. This specification develops the language, its
substitution operations, its semantics, and its thirteen primitive inference rules.
It proves soundness by induction on typed derivations, then gives direct
constructions for definition and specification interpretations and witnessed
subtype carriers. The proof order makes the semantic premises explicit and
avoids assuming the rule preservation that the soundness theorem must establish.

The intrinsically typed development in Lean 4 checks the core results. Named
syntax, scoped lookup, theorem provenance, and frontend elaboration are described
as implementation contracts. Their connection to the checked calculus requires
a separate refinement proof.

#v(0.8em)
#keyblock("info", [Reading Guide], [
  Part I develops the mathematics and gives proofs next to the results they
  justify. Blue annotations identify the corresponding Lean definitions and
  theorems. Named boundary contracts in Part I are marked explicitly where they
  require implementation refinement. Part II retains the engineering design,
  conformance duties, and dictionary-passing blueprint. The appendices collect
  dependencies, validation scenarios, and proof locations.
])

#outline(title: [Contents], depth: 2)

#pagebreak(weak: true)

#set heading(numbering: "1.")

= Part I: Logic Core (Normative)

#keyblock("warning", [Proof Scope], [
  The sole formal proof line is `formal_verification/QEDFV/HOL`; the root
  `QEDFV` module imports `HOL/Soundness.lean`. The core package is
  `typed_hol_core_proof_complete`. It proves the typed core, including
  `ADD_ASSUM` and witness-based choice, plus the stated fixed-signature semantic
  extension results and the object-language infinity rule. The history-indexed
  development provides both the extension introduction relation and the full
  fixed-signature `HistoryDerivation` closure, which chains extension products
  with the supported core rules and is sound at the history's model pair. It does
  not yet prove a derivability-preserving calculus for growing theories,
  syntactic erasure, or refinement of the MoonBit implementation. The removed
  approximation modules are not proof evidence.
])

The normative mathematical core consists of indexed types and terms, typed
substitutions, the thirteen-constructor derivation relation, and the interpretation
specified below. The signature is fixed throughout each derivation. Extension
contracts change an interpretation of that signature; their precise scope is
stated separately from derivability.

The named syntax and state policies describe how an implementation should expose
this core. They do not add constructors to the checked derivation relation.
Part II adds no logical authority. A discrepancy between the prose and Lean is
an obligation to reconcile their definitions, rather than a license to infer a
stronger theorem from implementation tests.

#pagebreak(weak: true)

= Notation and Meta-Level Conventions

We use separate notation for the objects that play different roles in the proof.
A type context is an ordered list $Gamma$; an assumption list is $H$.
Type variables are $alpha_i$, types are $tau$ and $upsilon$, terms are $s,t,u$,
and propositions are $p,q$. A constant identifier is $c$, and its principal
schema is $Sigma(c)$. The identifier is not its user-visible name.

#table(
  columns: (1fr, 3fr), inset: 6pt, align: left,
  [*Notation*], [*Meaning*],
  [$Gamma tack.r_Sigma t : tau$], [A term in the indexed family $"Tm"_(Sigma)(Gamma,tau)$.],
  [$H tack.r_(Sigma,Gamma) p$], [Derivability by the thirteen primitive constructors.],
  [$H models_I p$], [Validity for the fixed signature and context under interpretation $I$.],
  [$D_(rho)(tau)$], [The carrier interpreting type $tau$ under type valuation $rho$.],
  [$E_(I,rho,eta)(t)$], [The value of term $t$ under constant interpretation $I$ and environment $eta$.],
  [$s =_tau t$], [Object-language equality at type $tau$; its result type is $"bool"$.],
  [$s = t$], [Equality of mathematical objects in the surrounding metatheory.],
  [$t[theta]$, $t[sigma]$], [Type instantiation and term substitution, respectively.],
  [$H ++ K$], [Concatenation of finite assumption lists.],
  [$"del"(H,p)$], [The list obtained by deleting every occurrence structurally equal to $p$.],
  table.hline(stroke: 0.6pt + ink),
)

Once a signature and context have been fixed in a subsection, we abbreviate
$H tack.r_(Sigma,Gamma) p$ to $H tack.r p$. Empty assumptions are written
$[] tack.r p$. This convention does not identify a type context with an
assumption list. Similarly, $E(t)$ abbreviates $E_(I,rho,eta)(t)$ only when those
parameters have just been fixed. We restore the parameters when changing the
environment or valuation.

Named binders provide a readable presentation of De Bruijn terms. When named
syntax is discussed, $s equiv_alpha t$ means alpha-equivalence. It is not equality
of arbitrary implementation data. The relation $models$ is semantic validity;
the relation $tack.r$ is derivability. Neither is used as shorthand for the other.

The exposition follows Steven G. Krantz's _A Primer of Mathematical Writing_
(second edition), especially Sections 1.8 and 2.2--2.4: introduce notation before
use, keep it consistent, state hypotheses with the theorem, and explain the
structure of a proof in prose. The writing reference is
#link("https://arxiv.org/pdf/1612.04888")[arXiv:1612.04888].

= Motivation and Design Goal

The central engineering goal of QED is to separate trusted reasoning from untrusted proof search. In an LCF architecture, theorem creation is restricted to a very small set of primitive kernel operations. Everything else, including automation and tactics, is merely a theorem-producing program that calls those primitives.

This architecture has two consequences:

1. Correctness is reduced to the soundness of a small kernel.
2. Rich user tooling can evolve without expanding the trusted code base.

The mathematical role of this document is to state the object language and inference rules precisely enough to support both consequences.

= Positioning and Related Systems

QED is positioned as a minimal, auditable HOL kernel rather than a full proof-assistant platform. The design goal is to keep the trusted core small, make boundary assumptions explicit, and allow tactic/automation layers to evolve independently.

#definition([Design Target])[
QED prioritizes kernel verifiability over feature breadth: every exported theorem object must be traceable to primitive kernel rules under explicit side conditions.]

Compared with mainstream systems:

- HOL Light: same LCF trust model and primitive-rule discipline, but QED uses typed De Bruijn terms in the checked calculus and named terms at the implementation boundary.
- Coq: richer dependent type theory and broader automation ecosystem, while QED currently focuses on STT/HOL kernel minimality.
- Isabelle: mature logical framework and extensive libraries, while QED intentionally optimizes for a compact, audit-oriented kernel specification.

= Foundational Theory

== Signatures and Symbols

#definition([Checked type language])[The set of types is generated by
$
  tau ::= alpha_i | "bool" | "ind" | (tau -> upsilon) | k(tau_1,...,tau_n), quad i,k,n in NN.
$
Function types associate to the right. The two base types and the arrow
constructor are fixed. A constructor node $k(tau_1,...,tau_n)$ is the Lean
`Ty.con k n args` with `args : Fin n -> Ty`; the identifier $k$ and arity $n$ are
plain numbers. Arity correctness of a particular $k$ is not part of `Ty`: it is a
side condition of any later gate that introduces $k$. This is the language
implemented by `Ty`. No constructor identifier other than the fixed base types has
a declared meaning in this development yet.]

#definition([Constructor interpretation])[A constructor interpretation $kappa$
assigns to every identifier $k$, arity $n$ and tuple of carriers
$(X_1,...,X_n)$ a carrier $kappa(k,n,X_1,...,X_n)$. It is an explicit parameter
of the semantics, separate from the valuation $rho$ of type variables. The
default interpretation sends every constructor to the one-point carrier.]

#definition([Constant signature])[A signature is a function $Sigma : NN -> "Ty"$.
The value $Sigma(c)$ is the principal type schema of identifier $c$. In
particular, every identifier has a schema slot. A semantic extension below
changes the value assigned to a slot, rather than growing this function's domain.
The type variables in a schema are instantiated at each occurrence.]

A scoped map from names to identifiers serves the implementation's resolver.
It is distinct from $Sigma$: changing name lookup does not itself change a term
whose identifiers are fixed. The general `TyApp` representation and global
history policies are described below as interface contracts.

#lean-def("Types", ("Ty", "TyConVal", "defaultTyCon"))
#lean-def("Terms", ("Signature",))

== Constant Type Schemes and Instance Relation

#definition([Type substitution])[A type substitution is a total map $theta$
from type-variable identifiers to types. An untouched variable is mapped to
itself. Extend the map recursively, keeping base types fixed and acting on both
components of an arrow type. We write the result as $tau[theta]$.]

Write $tau prec.eq upsilon$ when $tau$ is an instance of the schema $upsilon$,
that is, when $tau=upsilon[theta]$ for some $theta$. A constant occurrence records this substitution: $c[theta]$ has
type $Sigma(c)[theta]$. An instance relation alone would hide the witness;
recording $theta$ gives the evaluator the valuation needed for that occurrence.

For example, a constant with schema $alpha_0 -> alpha_0$ may be used at
$"bool" -> "bool"$ and at $"ind" -> "ind"$. These are distinct instances of
one identifier, not separately declared constants.

#lean-def("Terms", ("Term.const",))

== Logical Constants and Reserved Symbols

Equality and choice are intrinsic term constructors. For each type $tau$, their
types are
$
  "eq"_tau : tau -> tau -> "bool", quad
  epsilon_tau : (tau -> "bool") -> tau.
$
The notation $s =_tau t$ abbreviates $"eq"_tau s t$. The notation $epsilon_tau P$
denotes choice applied to a predicate. Neither constructor performs signature
lookup; neither can be replaced by defining an ordinary constant.

The MoonBit surface spellings `=` and `@` are reserved. The resolver must map
them to these logical roles and reject an attempt to rebind them. This is an
implementation requirement, rather than a side condition on the intrinsic
constructors.

#proposition([Semantic choice property])[Let $A$ be a nonempty carrier and
$P:A -> "Prop"$ a predicate. The selector used in the semantics satisfies
$
  (exists x in A. P(x)) => P(epsilon_(A)(P)).
$
*Proof.* If the predicate has a witness, define the selected value to be a
classically chosen witness. Otherwise choose an arbitrary inhabitant of $A$.
In the first case, the chosen witness satisfies $P$ by construction; the second
case cannot occur under the displayed hypothesis.]

#lean-def("Evaluation", ("select",))
#lean-proof("Evaluation", ("select_spec",))

The displayed implication is a statement in the metatheory. It justifies the
witness-based `SPECIFY` rule below; it is not an arbitrary axiom-admission rule.

#note([Equality formation])[If $Gamma tack.r_Sigma s:tau$ and
$Gamma tack.r_Sigma t:tau$, then $Gamma tack.r_Sigma (s =_tau t):"bool"$.
The shared type is necessary: equality is not defined between values of different
carriers. This is enforced by the constructors, not repaired after construction.]

#lean-def("Terms", ("Term.eq", "Term.choice", "Term.equal"))

== Object-Language Propositional Connectives and Quantifiers

The term grammar also contains constructors for truth, falsity, conjunction,
implication, universal quantification, and existential quantification. These
are object-language terms of type `bool`, not abbreviations in Lean's
metalogic. Quantifiers bind the first type in the context; the remaining
context is unchanged.

#block(sticky: true)[
  For $p,q : "Tm"_(Sigma)(Gamma,"bool")$ and
  $r : "Tm"_(Sigma)(tau :: Gamma,"bool")$, their semantic clauses are:
]

$
  E("true") &= "True", \
  E("false") &= "False", \
  E(p "and" q) &= E(p) and E(q), \
  E(p "implies" q) &= (E(p) => E(q)), \
  E("all"_tau r) &= forall x in D_(rho)(tau). E_(eta[x])(r), \
  E("ex"_tau r) &= exists x in D_(rho)(tau). E_(eta[x])(r).
$

Here $eta[x]$ extends the environment with $x$ at the distinguished binder.
Each equation follows by unfolding the corresponding evaluator clause; no
logical soundness premise is built into the model. Renaming and term
substitution commute with the binders by lifting their maps, while type
instantiation transports bound values along the carrier equality
$D_(rho)(tau[theta]) = D_(theta^* rho)(tau)$.

#lean-def("Terms", ("Term.truth", "Term.falsity", "Term.conj", "Term.imp", "Term.all", "Term.ex"))
#lean-proof("Evaluation", ("Term.eval_truth", "Term.eval_falsity", "Term.eval_conj", "Term.eval_imp", "Term.eval_all", "Term.eval_ex", "Term.eval_rename", "Term.eval_substitute"))
#lean-proof("Instantiation", ("Term.eval_instType",))

== Signature Judgments for Scoped Stacks

#contract([Implementation contract])[The following finite-map rules specify name lookup;
they are not additional operations on the checked fixed signature $Sigma$.]


#definition([Scoped Signature Judgments])[
We use the following judgments for scoped signature operations:

- $S tack.r "wf"$: signature stack $S$ is well-formed.
- $S tack.r c : tau$: lookup for constant $c$ succeeds with type $tau$.
- $S tack.r "push" mapsto S'$: push succeeds and returns $S'$.
- $S tack.r "add"(c : tau) mapsto S'$: insertion in current scope succeeds.
- $S tack.r "pop" mapsto S'$: pop succeeds and returns $S'$.]

Notation: $S "++" [F]$ denotes stack append with $F$ as the new innermost frame. In particular, $S "++" ["empty"]$ means push one fresh empty scope onto $S$.

Representative rules:

$
  (S tack.r "wf")
  /
  (" "S tack.r "push" mapsto S "++" ["empty"]" ")
$

$
  (" "S = [S_0, ..., S_n] , c in.not "dom"(S_n) , S' = [S_0, ..., S_n[c := tau]]" ")
  /
  (S tack.r "add"(c : tau) mapsto S')
$

$
  (" "S = [S_0, ..., S_n] , c in "dom"(S_n) , S_(n)(c) = tau" ")
  /
  (S tack.r c : tau)
$

$
  (" "S = [S_0, ..., S_n] , c in.not "dom"(S_n) , [S_0, ..., S_(n - 1)] tack.r c : tau" ")
  /
  (S tack.r c : tau)
$

$
  (" "S = [S_0, ..., S_n] , n > 0 , S' = [S_0, ..., S_(n - 1)]" ")
  /
  (S tack.r "pop" mapsto S')
$

#note([Well-Formedness Side Conditions])[
- no frame may bind a reserved logical symbol;
- each frame is a finite partial map;
- lookup is deterministic by innermost-first traversal.]

These rules make success/failure boundaries explicit and give a judgmental presentation of scoped lookup and mutation.

== Global Theory State vs Local Scope State

#contract([Implementation contract])[A global declaration history must distinguish
compatible extensions from sibling histories. Local name lookup alone is
insufficient for theorem provenance; theorem handles therefore carry their
originating lineage and are accepted only along compatible history prefixes.]


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

Equivalent representation view: `"DefHeads"(T)` is any monotone history set unaffected by scope pop.

Monotonicity law:
$
  T mapsto T' arrow.r.double "DefHeads"(T) subset.eq "DefHeads"(T')
$

#proposition([Pop Invariance of Definitional History])[
If $(T_0, S) tack.r "pop" mapsto (T_1, S')$, then
$
  T_0 = T_1 and "DefHeads"(T_0) = "DefHeads"(T_1)
$
trivially, because `pop` is local-scope-only and does not rollback committed theory symbols.]

== Type Grammar and Carrier Interpretation

Let $rho$ assign a small carrier to each type variable. It is _admissible_ if
each assigned carrier is nonempty. The checked interpretation uses propositions
as boolean values, natural numbers as individuals, and full function spaces:
$
  D_(rho)("bool") &= "Prop", & D_(rho)("ind") &= NN, \
  D_(rho)(alpha_i) &= rho(i), & D_(rho)(tau -> upsilon) &= D_(rho)(tau) -> D_(rho)(upsilon).
$
This interpretation fixes the meaning of the base types. It does not quantify
over arbitrary interpretations of the logical equality or choice constructors.

#proposition([Nonempty carriers])[Fix a constructor interpretation $kappa$. A pair
$(kappa, rho)$ is admissible when every variable carrier $rho(i)$ is nonempty and,
for every $k$, $n$ and tuple of nonempty carriers, $kappa(k,n,dots)$ is nonempty.
For every admissible pair and every type $tau$, the carrier $D_(kappa,rho)(tau)$
is nonempty.]

#proof(none)[Induct on $tau$. A boolean carrier contains the proposition True, and
the individual carrier contains zero. A variable carrier is nonempty by
admissibility. For an arrow type, choose an element $b$ of its codomain using the
induction hypothesis. The constant function with value $b$ inhabits the arrow
carrier. For a constructor node the induction hypothesis makes every argument
carrier nonempty, so the second admissibility clause makes the constructor
carrier nonempty. These five cases exhaust the type grammar. If $kappa$ violates
the second clause, no $rho$ is admissible and every sequent is vacuously valid
under that $kappa$; every core theorem below is therefore stated for all
constructor interpretations $kappa$ with no further hypothesis.]

#lean-def("Types", ("Ty.denote", "Admissible"))
#lean-proof("Types", ("Ty.carrier_nonempty",))

== Type Constructor Extension Discipline

The implementation's broader type syntax may represent $k(tau_1,...,tau_n)$ by
`TyApp(k, args)`, with constructor arity checked against a type signature. A
faithful extension must supply the new carrier and preserve type-substitution
coherence. The checked `Ty` language has the neutral node `Ty.con` for such a $k$
and an explicit constructor interpretation. We first state the semantic subtype
construction on its own; the later section on type-definition gate semantics
connects it to a gate that allocates a $k$ and fixes its carrier.

#definition([Witnessed predicate family])[Fix a representation type $tau$.
For every admissible valuation $rho$, let $P_rho$ be a predicate on $D_(rho)(tau)$,
and require a witness $w_rho$ satisfying it. Define
$
  A_rho = {x in D_(rho)(tau) : P_(rho)(x)}.
$
This is a semantic subtype, not a new type expression in the checked grammar.]

#proposition([Representation and abstraction])[There are maps
$"rep"_rho:A_rho -> D_(rho)(tau)$ and $"abs"_rho:D_(rho)(tau) -> A_rho$ such that
$
  "abs"_(rho)("rep"_(rho)(a)) &= a && (a in A_rho), \
  P_(rho)("rep"_(rho)(a)) &&& (a in A_rho), \
  "rep"_(rho)("abs"_(rho)(x)) &= x && (P_(rho)(x)).
$
The carrier $A_rho$ is nonempty.]

#proof(none)[The pair consisting of $w_rho$ and its witness proof inhabits $A_rho$.
Let $"rep"_rho$ forget the proof component. For $"abs"_(rho)(x)$, use $x$ itself
when $P_(rho)(x)$ holds; otherwise use the chosen witness. For a subtype value
$a$, its property makes the first branch apply to $"rep"_(rho)(a)$, and proof
irrelevance gives the original subtype value. The range statement is the
property component of $a$. Under the hypothesis $P_(rho)(x)$, the first branch
also proves the last equation.]

#lean-proof("TypeDefinitions", ("TypeDefContract.nonempty", "TypeDefContract.abs_rep", "TypeDefContract.rep_in_range", "TypeDefContract.rep_abs_of_pred"))

#contract([Implementation contract (TypeDefOK)])[To add a syntactic constructor $k$ of
arity $n$, an implementation must also check global freshness of $k$ and its
Abs/Rep identifiers, closure of the predicate under the declared type parameters,
and a nonemptiness witness at every parameter instantiation. It must expose
Abs/Rep at the appropriate types and provide the three displayed laws as
justified theorem products. The semantic construction supplies the carrier
mathematics; it does not prove that this registration procedure is correct.]

#keyblock("warning", [Signature Integration Boundary], [
  `TypeDefContract` records the witnessed family at the carrier level, and the
  legacy `Extension.typeDefinition` leaves the constant interpretation unchanged;
  neither allocates a type constructor. The gate `TypeDefGate` and the model step
  `TypeDefGate.interpret` (section on type-definition gate semantics) allocate a
  constructor and define the new model, over model pairs `(κ, I)`. They are the
  `typedef` constructor of `ExtensionDerivation` (section on history-indexed
  derivations), so the three Abs/Rep laws are derivable at the extended history from a
  hypothesis-free witness derivation; histories are interpreted over model pairs.
  History freshness of `k`, Rep and Abs is a carried side condition that the
  semantic soundness induction does not use, but it is required to form
  well-formed histories. The signature stays total. Consequences that chain the
  derived laws with core rules use `HistoryDerivation`; syntactic erasure of a
  definition is proved (`HistoryDerivation.erase_definition`), that of a specification, a
  type definition and the kernel's string-name lowering are not provided. The
  carrier proof must not be cited as a
  proof of the kernel's registration procedure.
])

== Term Grammar

#definition([Typed variables])[A context is a finite list of types, with the
newest binder first. The variable family is generated by
$
  "zero" in "Var"(tau :: Gamma,tau), quad
  frac(v in "Var"(Gamma,upsilon), "succ"(v) in "Var"(tau :: Gamma,upsilon)).
$
The variable at index zero names the newest binder; a successor refers past it.
A context may include free parameters of an open term. These parameters are
still typed positions, not ordinary signature constants.]

#definition([Intrinsic terms])[Write $"Tm"_(Sigma)(Gamma,tau)$ for the family
of terms of type $tau$ in context $Gamma$. Its twelve constructors are:

$
  frac(v in "Var"(Gamma,tau), Gamma tack.r_Sigma "var"(v):tau), quad
  frac(c in NN quad theta:"TypeSub", Gamma tack.r_Sigma c[theta]:Sigma(c)[theta]).
$
$
  frac(Gamma tack.r_Sigma f:tau -> upsilon quad Gamma tack.r_Sigma u:tau,
       Gamma tack.r_Sigma f u:upsilon).
$
$
  frac(tau :: Gamma tack.r_Sigma t:upsilon,
       Gamma tack.r_Sigma lambda_tau t:tau -> upsilon).
$
$
  Gamma tack.r_Sigma "true":"bool", quad
  Gamma tack.r_Sigma "false":"bool".
$
$
  frac(Gamma tack.r_Sigma p:"bool" quad Gamma tack.r_Sigma q:"bool",
       Gamma tack.r_Sigma p "and" q:"bool"), quad
  frac(Gamma tack.r_Sigma p:"bool" quad Gamma tack.r_Sigma q:"bool",
       Gamma tack.r_Sigma p "implies" q:"bool").
$
$
  frac(tau :: Gamma tack.r_Sigma p:"bool",
       Gamma tack.r_Sigma "all"_tau p:"bool"), quad
  frac(tau :: Gamma tack.r_Sigma p:"bool",
       Gamma tack.r_Sigma "ex"_tau p:"bool").
$
$
  Gamma tack.r_Sigma "eq"_tau:tau -> tau -> "bool", quad
  Gamma tack.r_Sigma epsilon_tau:(tau -> "bool") -> tau.
$
Here $lambda_tau t$ is the stored abstraction; $lambda x:tau. t$ is its named
presentation. Domain and codomain constraints are part of the family indices.
A malformed application is therefore not an element of a larger untyped family
awaiting a later validity check.]

#lean-def("Terms", ("Var", "Term", "Term.equal"))

#note([Named presentation])[The surface grammar retains variables $x:tau$, constant
names, application, and named abstraction. A common representation uses
`Var(name, tau)`, `Const(name, tau)`, `Comb(f, x)`, and `Abs(x, t)`.
Resolution must distinguish a name used as a variable from one used as a
constant, and attach a fixed identifier and schema instance to each constant.
The conversion contract below explains this boundary.]

#keyblock("warning", [Binding and Capture], [
  Names are a presentation device. Substitution acts on typed variable positions
  and must lift a replacement beneath a new binder. Replacing a name by raw text
  would permit capture and would invalidate the beta proof.
])

== Resolution Boundary (Integrated Form)

#contract([Implementation contract])[The following named-resolution judgment specifies
the bridge an implementation must provide; it is not another Lean term grammar.]


#definition([One-Shot Resolution])[
To avoid splitting the document into two full grammars, QED keeps one named grammar and adds a single boundary judgment:
$
  Sigma_c tack.r t mapsto t_r
$
where $t_r$ is a resolved term used by kernel rules. Constant occurrences are frozen at resolution time and are not re-looked-up during later theorem reuse.]

The operational resolver is written with $mapsto$; named structural
elaboration uses $arrow.b.double$. These denote related interface operations,
not an identification with the core derivability judgment.

Representative constant-resolution clause:
$
  (" "Sigma_c tack.r c : tau , "resolve"(Sigma_c, c) = kappa_c" ")
  /
  (" "Sigma_c tack.r c : tau mapsto "ConstAtom"(kappa_c, tau)" ")
$

#property([Theorem Stability Under Scope Mutation])[
If a theorem is constructed from resolved terms, then later `push`/`pop`/shadowing operations on $Sigma_c$ do not change that theorem's stored terms or established typing. Semantic
stability additionally requires compatible declaration history.]

#property([Alias Safety for Existing Theorems])[
Theorem aliasing is handle-level only: alias creation does not trigger re-elaboration, and therefore does not depend on the current signature stack.]

= Elaboration and Core Typing Judgments

#contract([Named interface contract])[This section retains the external typing and
resolution design. The intrinsic family already enforces core typing; the
MoonBit-to-family translation is an implementation refinement obligation.]


For the named interface, let $Gamma_"n"$ be an ordered context of named bindings.
A binder shadows an earlier binding of the same name; variable lookup selects
the newest matching position. Erasing names gives the intrinsic type context
$Gamma$. Thus $Gamma_"n"$ and $Gamma$ are related contexts, not one object used
with two incompatible meanings. In the interface formulas, $"fun"(tau,upsilon)$
is the representation of the arrow type $tau -> upsilon$.

== Named Elaboration Judgment

Named terms are first elaborated against the current signature stack:
$
  Sigma_c ; Gamma_"n" tack.r t arrow.b.double t_r
$
where $t_r$ is a resolved term in which constant occurrences have fixed kernel identities.

Representative clauses:

$
  (" "(x : tau) in Gamma_"n"" ")
  /
  (" "Sigma_c ; Gamma_"n" tack.r x : tau arrow.b.double "RVar"(x, tau)" ")
$

$
  (" "Sigma_c tack.r c : tau_"gen" , "resolve"(Sigma_c, c) = kappa_c , tau prec.eq tau_"gen"" ")
  /
  (Sigma_c ; Gamma_"n" tack.r c : tau arrow.b.double "RConst"(kappa_c, tau))
$

$
  (" "Sigma_c ; Gamma_"n" tack.r f arrow.b.double f_r ," "Sigma_c ; Gamma_"n" tack.r x arrow.b.double x_r" ")
  /
  (Sigma_c ; Gamma_"n" tack.r f" "x arrow.b.double "RComb"(f_r, x_r))
$

$
  (" "Sigma_c ; (Gamma_"n", x : tau) tack.r t arrow.b.double t_r" ")
  /
  (" "Sigma_c ; Gamma_"n" tack.r lambda (x : tau). t arrow.b.double "RAbs"(x, tau, t_r)" ")
$

Elaboration failure is explicit and does not produce a theorem object.

== Core Typing over Resolved Terms

Primitive rules consume resolved terms only. Their typing judgment is:
$
  Gamma_"n" tack.r.r t_r : tau
$
with rules independent of mutable signature lookup.

Representative clauses:

$
  (" "(x : tau) in Gamma_"n"" ")
  /
  (" "Gamma_"n" tack.r.r "RVar"(x, tau) : tau" ")
$

$
  (" "kappa_c : tau_"gen" , tau prec.eq tau_"gen"" ")
  /
  (" "Gamma_"n" tack.r.r "RConst"(kappa_c, tau) : tau" ")
$

$
  (" "Gamma_"n" tack.r.r f_r : "fun"(tau_1, tau_2) ," "Gamma_"n" tack.r.r x_r : tau_1" ")
  /
  (Gamma_"n" tack.r.r "RComb"(f_r, x_r) : tau_2)
$

$
  (Gamma_"n", x : tau_1 tack.r.r t_r : tau_2)
  /
  (" "Gamma_"n" tack.r.r "RAbs"(x, tau_1, t_r) : "fun"(tau_1, tau_2)" ")
$

#lemma([Polymorphic Constant Instantiation Admissibility])[
If $kappa_c : tau_"gen"$ and $tau prec.eq tau_"gen"$, then `"RConst"(kappa_c, tau)` is a well-formed resolved term and may appear in any rule premise requiring type $tau$.]

#remark([No Monomorphic Lockout])[
A constant introduced once at principal schema (e.g. $"fun"(alpha, alpha)$) is usable at all admissible instances (e.g. $"fun"("bool", "bool")$, $"fun"("ind", "ind")$), rather than requiring one separately named constant per instance type.]

== Stability Theorem for Scope Mutation

#theorem([Resolved-Theorem Stability Under Scope Mutation])[
If $Sigma_c ; Gamma_"n" tack.r t arrow.b.double t_r$ and $Gamma_"n" tack.r.r t_r : tau$, then for any later signature stack mutation sequence $mu$ (push/pop/shadowing on non-reserved names), the established typing fact for $t_r$ remains valid:
$
  Gamma_"n" tack.r.r t_r : tau
$
because $t_r$ contains fixed resolved constant identities and does not re-run named lookup.]

This argument establishes an abstract lookup invariant for fixed identities.
A concrete refinement must also prove that identifiers denote the same
declaration history; the argument alone cannot justify sibling-state reuse.

= Substitution and Alpha-Equivalence

== Type Substitution

For a total variable substitution $theta$, the recursive equations are
$
  "bool"[theta] &= "bool", & "ind"[theta] &= "ind", \
  alpha_i[theta] &= theta(i), & (tau -> upsilon)[theta] &= tau[theta] -> upsilon[theta].
$
Let $iota(i)=alpha_i$ be the identity substitution. Define composition by
$(theta compose psi)(i)=psi(i)[theta]$: the rightmost substitution acts first.

#proposition([Identity and composition])[For every type $tau$,
$
  tau[iota]=tau, quad (tau[psi])[theta]=tau[theta compose psi].
$
*Proof.* Induct on $tau$. Base types are fixed and the variable case is the
definition of composition. In the arrow case, apply the induction hypotheses
to the domain and codomain. No constant schema or environment is involved.]

#lean-proof("Types", ("Ty.subst_id", "Ty.subst_comp"))

Type instantiation also acts on the context and every type annotation in a term.
A constant occurrence $c[psi]$ becomes $c[theta compose psi]$. This clause ensures
that the principal schema remains $Sigma(c)$ while its instance changes.

#lean-def("Terms", ("Var.mapTypes", "Term.instType"))

== Type-Variable Support

For a type, $"TVars"(tau)$ is its set of variable identifiers. For terms,
the closure gates use the exact function defined by `Term.typeVars`:
$
  "TVars"("var"(v:tau)) &= "TVars"(tau), \
  "TVars"(c[theta]) &= "TVars"(Sigma(c)[theta]), \
  "TVars"(f u) &= "TVars"(f) union "TVars"(u), \
  "TVars"(lambda_tau t) &= "TVars"(t), \
  "TVars"("eq"_tau) &= "TVars"(tau), \
  "TVars"(epsilon_tau) &= "TVars"(tau).
$
In particular, this function does not separately add an unused binder's domain
type. It must not be confused with a traversal collecting every stored type
annotation. The later closure propositions refer to this defined support.

#lean-def("Types", ("Ty.typeVars",))
#lean-def("Terms", ("Term.typeVars",))

#definition([Annotation support and constructor support])[Evaluation depends on
every type annotation of a term, including the domain of an unused binder, so two
further functions are used by the congruence results below. $"AVars"(t)$ is
defined like $"TVars"(t)$ except that
$"AVars"(lambda_tau t) = "TVars"(tau) union "AVars"(t)$; it contains
$"TVars"(t)$ and the variables of the type of $t$. The constructor support
$"Cons"(tau)$ is the set of constructor identifiers occurring in a type, with
$"Cons"(k(tau_1,...,tau_n)) = {k} union "Cons"(tau_1) union dots.c union "Cons"(tau_n)$.
For terms, $"Cons"(t)$ is defined by the same clauses as $"AVars"$, collecting
constructor identifiers from variable and binder types and from the schema
instances of constants; it contains $"Cons"$ of the type of $t$. Type
substitution acts on both supports by
$"Cons"(tau[theta]) = "Cons"(tau) union union.big_(i in "TVars"(tau)) "Cons"(theta(i))$, and instantiation of a term acts on
$"Cons"(t)$ in the same way over $"AVars"(t)$.]

#lean-def("Types", ("Ty.tyCons", "TyConVal.AgreeOn", "TyConVal.IsAdmissible"))
#lean-def("Terms", ("Term.annotVars", "Term.tyCons"))
#lean-proof("Types", ("Ty.tyCons_subst",))
#lean-proof("Terms", ("Term.tyCons_instType", "Term.typeVars_subset_annotVars"))

== Renaming and Weakening

A renaming $r in "Ren"(Gamma,Delta)$ assigns to each variable in $Gamma$ a variable of
the same type in $Delta$. The family $"Ren"(Gamma,Delta)$ consists of these type-preserving
variable maps. Its lift $r^+$ fixes the new zero variable
and sends $"succ"(v)$ to $"succ"(r(v))$.

Renaming acts recursively on terms. In particular,
$
  (f u)[r]=f[r] u[r], quad (lambda_tau t)[r]=lambda_(tau)(t[r^+]).
$
Constants, equality, and choice are unchanged. Weakening is the renaming
$v mapsto "succ"(v)$; write $"wk"(t)$ for its action. It embeds an old term
under a new binder without binding an old variable.

#lean-def("Terms", ("Ren", "Ren.lift", "Term.rename"))
#lean-def("Rules", ("weakenTerm", "weakenSequent"))

== Term Substitution

A typed substitution $sigma in "Sub"_(Sigma)(Gamma,Delta)$ assigns to each variable of type
$tau$ in $Gamma$ a term in $"Tm"_(Sigma)(Delta,tau)$. All replacement terms live
in the same target context and are read simultaneously. The lift is
$
  sigma^+("zero")="var"("zero"), quad
  sigma^+("succ"(v))="wk"(sigma(v)).
$
Substitution on terms is defined by
$
  "var"(v)[sigma] &= sigma(v), \
  (f u)[sigma] &= f[sigma] u[sigma], \
  (lambda_tau t)[sigma] &= lambda_(tau)(t[sigma^+]).
$
Constants, equality, and choice are unchanged. These are the complete recursive
cases together with the three fixed constructors. Type preservation follows
from the typed map and the indexed result family.

#lean-def("Terms", ("Sub", "Sub.lift", "Term.substitute"))

#example([Parallel swap])[In context $[tau,tau]$, assign each of the two
variables to the other. The substitution exchanges their occurrences in one
step. It does not rewrite the replacement term of one entry using the other
entry. This distinction matters in the instantiation rule.]

== De Bruijn Substitution for Beta

For $u in "Tm"_(Sigma)(Gamma,tau)$ define the single substitution $[u]$
from $tau :: Gamma$ to $Gamma$ by
$
  [u]("zero")=u, quad [u]("succ"(v))="var"(v).
$
Thus $t[u]$ removes the newest binder and replaces its occurrences by $u$.
The context indices perform the shift-back safely; no negative index arithmetic
is required in the checked operation.

#example([Capture avoidance])[The named term
$(lambda x:tau. lambda z:tau. x)y$, with free $y:tau$, contracts to
$lambda z:tau. y$. Its body represents $x$ as successor-of-zero beneath $z$.
Lifting the replacement shifts $y$ past $z$, so the result still refers to
$y$, not to the zero variable $z$.]

#lean-def("Terms", ("Sub.single",))

An integer-index implementation may express the same intended operation as
$
  "shift"(-1,0,"subst"(0,"shift"(1,0,u),t)).
$
This equation describes an implementation algorithm on well-scoped inputs; a
refinement must connect it to the typed single substitution. It is not the
Lean definition and is not used as an unproved lemma in soundness.

== Alpha-Equivalence and the Named Boundary

Two named terms are alpha-equivalent when they differ only in the spellings of
bound variables. A correct conversion sends them to the same typed De Bruijn
term and preserves free-variable positions, constant identities, and type labels.
Reflexivity, symmetry, transitivity, and constructor congruence are requirements
on this named relation.

In the intrinsic core, bound-variable names do not exist. Structural equality
already ignores their spelling while retaining type indices. Hence there is no
need to quotient the core term datatype again by a named alpha relation. The
following boundary section states the precise obligations for named input.

= Boundary Conversion and Scoped Shadowing

#keyblock("warning", [Implementation Refinement Contract], [
  This section retains the detailed named/De Bruijn and scope design. The
  conversion functions below are interface requirements, not retained Lean
  approximation proofs. Their concrete denotation and typing correspondence
  with MoonBit remains to be proved. Abstract implications are justified below
  with their conversion hypotheses explicit.
])

The executable propositional prelude presents connectives as defined constants,
whereas the Typed HOL syntax uses primitive constructors for truth, falsity,
conjunction, implication, and the two quantifiers. A refinement proof must map
each kernel definition to its corresponding object-language constructor and
prove the defining equation is preserved by lowering, evaluation, and
substitution. Derived connectives such as negation and disjunction must be
related compositionally to the primitive definitions. The executable infinity
registration is an audit marker, not a gate on the sentence: see the infinity
rule below.

QED currently uses a two-layer boundary:

- external-facing terms/theorems are in named syntax;
- kernel rule cores execute on De Bruijn syntax.

Write `NamedTerm` and `NamedSequent` for boundary presentations. A conversion
returns either a successfully converted object or failure; `Option` denotes
this alternative. The four interface maps have types:

$
  "Term"_arrow.b : "NamedTerm" arrow.r "Option"("DbTerm")
$
$
  "Term"_arrow.t : "DbTerm" arrow.r "Option"("NamedTerm")
$
$
  "Thm"_arrow.b : "NamedSequent" arrow.r "Option"("DbSequent")
$
$
  "Thm"_arrow.t : "DbSequent" arrow.r "Option"("NamedSequent")
$

Here $"Term"_arrow.b$ lowers named terms to De Bruijn terms, and $"Term"_arrow.t$ reconstructs named terms from De Bruijn terms. Likewise, $"Thm"_arrow.b$ lowers named sequents to De Bruijn sequents, and $"Thm"_arrow.t$ lifts De Bruijn sequents back to named boundary objects. All four conversions are partial and may fail at the boundary.

For theorem presentations, conversion acts on the sequent pair:
$
  "Thm"_arrow.b(A_p,p) mapsto (A_d,p_d), quad
  "Thm"_arrow.t(A_d,p_d) mapsto (A_p',p').
$
It is defined pointwise by $"Term"_arrow.b$ and $"Term"_arrow.t$ on assumptions and conclusion.

== Boundary Conversion Properties

The boundary metatheory relies on the following invariants.

#contract([Required boundary law (Alpha-Invariant Lowering)])[
$
  frac(t_1 equiv_alpha t_2 quad "Term"_arrow.b(t_1) mapsto d_1 quad "Term"_arrow.b(t_2) mapsto d_2, d_1 = d_2)
$]

#contract([Required boundary law (Round-Trip Stability up to Alpha)])[
$
  (" Term"_arrow.b" "t mapsto d ," Term"_arrow.t" "d mapsto t'" ")
  /
  (t' equiv_alpha t)
$]

#contract([Required boundary law (Lift Choice Congruence)])[
If $"Term"_arrow.t" "d mapsto t_1$ and $"Term"_arrow.t" "d mapsto t_2$, then $t_1 equiv_alpha t_2$.]

#property([Name-Insensitive Rule Matching])[
Any named-side premise matching required by primitive rules is interpreted modulo $equiv_alpha$. Binder spellings are presentation-level choices and cannot change rule applicability.]

#lemma([Type-Sensitive Core Matching])[
Boundary lowering preserves binder-domain type labels. Therefore, if two named abstractions differ in binder-domain type, their lowered typed De Bruijn forms are not structurally equal:
$
  "Term"_arrow.b" "(lambda (x : tau_1). t_1) eq.not "Term"_arrow.b" "(lambda (y : tau_2). t_2)
$
whenever $tau_1 eq.not tau_2$, even if bodies are De Bruijn-index isomorphic.]

#contract([Required boundary law (Term denotation preservation)])[Define a named
evaluator $E^"n"$ for the interface and an environment conversion sending a
named valuation $nu$ in $Gamma_"n"$ to its indexed environment $eta$ in $Gamma$.
On a successful lowering $"Term"_arrow.b(t) mapsto d$, require
$
  E^"n"_(I,rho,nu)(t)=E_(I,rho,eta)(d).
$
Both sides use the same constant interpretation and corresponding variable
positions, with their result carriers identified. Successful lifting must
satisfy the analogous equation in the reverse direction.]

#contract([Required boundary law (Sequent denotation preservation)])[Let
$"Thm"_arrow.b(H_"n",p_"n") mapsto (H_d,p_d)$. Under corresponding
environments, require satisfaction of $H_"n"$ to agree with satisfaction of
$H_d$, and require the conclusion values to agree. For validity equivalence,
the environment correspondence must cover all environments on both sides.
Successful lifting has the same requirement. Sequents here are pairs of lists
and conclusions; the notation does not assume that either pair has a derivation.]

#theorem([Semantic rule lifting safety])[Suppose a core rule consumes a finite
list of premise sequents and, on success, returns a conclusion sequent. Assume
it preserves validity whenever all its premises are valid. Assume the lowering
and lifting denotation laws just stated. Then the named rule obtained by
lowering all premises, applying the core rule, and lifting its result preserves
validity on successful runs.]

The theorem concerns denotation. Round-trip and alpha laws separately justify
the structural correspondence of boundary presentations.

#property([Diagrammatic Commutation on Successful Conversions])[
The lifting relation is visualized by the following commutative diagram (structural and semantic commutation):]

#align(center)[
  #diagram(
    node((0, 1.6), [$"NamedSequent" "/" equiv_alpha$]),
    node((2.0, 1.6), [$"NamedSequent" "/" equiv_alpha$]),
    node((0, 0), [$"DbSequent"$]),
    node((2.0, 0), [$"DbSequent"$]),
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
  "valid"(x) arrow.r.double "valid"(y)
$
under the denotation-preservation lemmas above.

#remark([Not a Strict Bijection])[
This correspondence is not a strict named-to-De Bruijn bijection:

- alpha-variant named terms collapse to one De Bruijn equivalence class;
- lifting from De Bruijn chooses a representative named binder presentation;
- boundary conversions are partial, so the mapping is defined only on well-formed successful cases.]

#keyblock("info", [Boundary Discipline], [
  Primitive rules are interpreted over `DbSequent` core objects. Named `Thm` values are boundary presentations. Conversion failure is a boundary failure, not a logical derivation.
])

#proof([of semantic lifting])[Suppose the named input is valid. The lowering
law makes its lowered sequent valid; preservation of the core rule makes the
core output valid; the lifting law makes the reconstructed named output valid.
The three implications compose. This argument is conditional on the two
boundary laws; it does not establish them for a particular converter.]

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

These operators provide the abstract logical calculus for scope push/add/pop.

Lookup is defined by:
$
  L(S, c) = S_(j)(c)
$
where $j$ is the greatest index such that $c in "dom"(S_j)$.

Insertion in current scope:
$
  A(S, c : tau)
$
is allowed iff $c in.not "dom"(S_n)$.

From these definitions:

#proposition([Shadowing Determinism])[
if $c$ is defined in innermost scope $S_n$, then $L(S, c) = S_(n)(c)$.
Proof. By definition, lookup returns $S_(j)(c)$ for the greatest index $j$ with
$c in "dom"(S_j)$. Since $c in "dom"(S_n)$ and $n$ is maximal index of the stack,
the greatest such index is $j = n$. Hence $L(S, c) = S_(n)(c)$.]

#proposition([Outer Restoration by Pop])[
if $S' = P(S)$, $A(S', c : tau_1) = S''$, and $Q(S'') = S$, then $L(S, c) = L(Q(S''), c)$.
Proof. $P(S)$ adds one fresh empty innermost frame. $A(S', c : tau_1)$ modifies only
that fresh frame. $Q$ then removes exactly that frame, restoring all original frames
pointwise. Therefore lookup of any symbol in restored stack is identical to lookup in $S$,
so $L(S, c) = L(Q(S''), c)$.]

#proposition([Scope-Local Uniqueness])[
if $c$ is already defined in innermost scope $S_n$, then $A(S, c : tau)$ fails.
Proof. Admissibility of $A(S, c : tau)$ requires $c in.not "dom"(S_n)$ by definition.
Given $c in "dom"(S_n)$, the premise is false, so no insertion rule instance exists; hence
$A(S, c : tau)$ fails.]

#theorem([Resolution Freeze under Scope Mutation])[
Let $mu$ be any finite sequence of operations from `{push, add, pop}` on non-reserved names,
and let $Sigma_c ; Gamma_"n" tack.r t arrow.b.double d$ with
$Gamma_"n" tack.r.r d:tau$ in the fixed resolved signature. If $mu$ is applied to obtain a later stack
$Sigma_c'$, then:
$
  Gamma_"n" tack.r.r d : tau
$
and all primitive-rule premises that mention $d$ are unchanged by $mu$.
Proof. $d$ contains resolved constant identities, not deferred name lookups. Scope mutations
alter only future named-resolution results; they do not rewrite existing resolved terms.]

These properties specify the abstract behavior required of any faithful scoped-signature realization.

Scope-local shadowing properties above are lookup properties only. They do not authorize redefining committed definition heads recorded in `"DefHeads"(T)`.

= Theorem Object and Trust Boundary

#definition([Sequent])[For fixed $Sigma$ and $Gamma$, a sequent consists of a
finite list $H$ of terms of type $"bool"$ and a conclusion $p$ of that type.
The same context types every assumption and the conclusion. We write the
sequent as $(H,p)$ and its derivability as $H tack.r_(Sigma,Gamma) p$.]

#lean-def("Rules", ("Sequent",))

== Assumption Lists and Their Semantic Reading

The checked syntax uses lists, not finite sets of alpha classes. We use $H ++ K$
for concatenation and $"del"(H,p)$ for deletion of every structurally equal
occurrence of $p$. Concatenation preserves order and multiplicity. In particular,
$H ++ H$ need not equal $H$ as syntax, and $H ++ K$ need not equal $K ++ H$.

Semantically, satisfying $H$ means satisfying each listed proposition. Repeated
occurrences impose no extra truth condition, and list order does not affect
satisfaction. This observation concerns the meaning of a list; it is not an
unproved exchange or contraction constructor in the derivation datatype.

#lean-def("Rules", ("union", "remove"))

A named implementation may normalize assumptions modulo alpha-equivalence.
Its normalization and theorem-acceptance rules must be related to the typed
list representation in a refinement proof. No finite-set law is assumed by
the thirteen-rule soundness argument below.

== The LCF Boundary

A theorem handle must carry justified derivability evidence, rather than only
a well-typed conclusion. External callers may request rule applications, but
must not fabricate accepted handles. Fixed constant identities must continue
to denote compatible declarations when the theorem is reused. An opaque data
constructor alone does not prove this history condition.

#keyblock("critical", [Kernel Integrity Condition], [
  The Lean relation proves soundness of derivations. To transfer this result to
  an executable kernel, every accepted handle must translate to justified
  evidence with the same interpretation. The MoonBit kernel records theorem
  origin lineage and rejects incompatible sibling histories; this is an
  implementation invariant covered by regression tests, while refinement to the
  Lean relation remains a separate obligation.
])

= Semantics and the Substitution Lemmas

== Environments and Constant Interpretations

Fix an admissible type valuation $rho$. An environment $eta$ assigns a value
in $D_(rho)(tau)$ to every variable of type $tau$ in $Gamma$. Write $eta[x]$ for
extension by $x$ at the new zero position; an outer successor reads its value
from $eta$.

A constant interpretation $I$ assigns, for every admissible valuation $rho$ and
identifier $c$, a value $I_(rho)(c) in D_(rho)(Sigma(c))$. The dependence on admissibility
is a proof argument in Lean and does not change the value. We do not assume
any rule-soundness law as a field of $I$.

#lean-def("Evaluation", ("Env", "ConstVal", "Env.extend"))

== Type Substitution in the Semantics

Define the induced valuation $rho_theta$ by $rho_(theta)(i)=D_(rho)(theta(i))$.
Nonemptiness of carriers makes this valuation admissible.

#lemma([Type interpretation commutes with substitution])[For every type $tau$,
$
  D_(rho)(tau[theta])=D_(rho_theta)(tau).
$
*Proof.* Induct on $tau$. The variable case is the definition of $rho_theta$;
both base cases are fixed. The arrow case follows from the two induction
hypotheses because both interpretations use the same full function space.]

#lean-proof("Types", ("Ty.denote_subst", "TypeSub.pull_admissible"))

The equality identifies the carriers used on the two sides. When evaluating a
constant occurrence $c[theta]$, read $I_(rho_theta)(c)$ and transport it along
this equality into $D_(rho)(Sigma(c)[theta])$. An interpretation is thus consulted
at the valuation of the principal schema, rather than at an arbitrarily chosen
value for each occurrence.

== Recursive Evaluation

Evaluation is determined by the twelve constructors. With $I,rho,eta$ fixed,
$
  E_(I,rho,eta)("var"(v)) &= eta(v), \
  E_(I,rho,eta)(c[theta]) &= I_(rho_theta)(c) quad "(after carrier identification)", \
  E_(I,rho,eta)(f u) &= E_(I,rho,eta)(f)(E_(I,rho,eta)(u)), \
  E_(I,rho,eta)(lambda_tau t) &= (x mapsto E_(I,rho,eta[x])(t)), \
  E_(I,rho,eta)("eq"_tau) &= (x mapsto (y mapsto x=y)), \
  E_(I,rho,eta)(epsilon_tau) &= epsilon_(D_(rho)(tau)).
$
For the logical constructors, write $E_x(p):=E_(I,rho,eta[x])(p)$. Their
semantic characterizations are:

$
  E("true") &= "True", \
  E("false") &= "False", \
  E(p "and" q) &= E(p) and E(q), \
  E(p "implies" q) &= (E(p) => E(q)), \
  E("all"_tau p) &= forall x in D_(rho)(tau). E_x(p), \
  E("ex"_tau p) &= exists x in D_(rho)(tau). E_x(p).
$

#lean-proof("Evaluation", ("Term.eval_truth", "Term.eval_falsity", "Term.eval_conj", "Term.eval_imp", "Term.eval_all", "Term.eval_ex"))

Object equality therefore means actual equality of denotations. At the boolean
type these denotations are propositions; propositional extensionality identifies
logically equivalent propositions. The arrow interpretation uses extensional
functions, which will justify abstraction congruence.

#lean-def("Evaluation", ("Term.eval",))
#lean-proof("Evaluation", ("Term.eval_equal",))

== Renaming and Term Substitution

#lemma([Renaming])[If $r in "Ren"(Gamma,Delta)$ is a typed renaming and $eta$ is an
environment for $Delta$, define $eta_(r)(v)=eta(r(v))$. Then
$
  E_(I,rho,eta)(t[r])=E_(I,rho,eta_r)(t).
$
*Proof.* Induct on $t$. Variables give the definition of $eta_r$, and fixed
constructors are unchanged. Application uses the two induction hypotheses. For
abstraction, evaluate both sides at an arbitrary argument $x$. The identity
$(eta[x])_(r^+)=eta_r[x]$ follows from the zero and successor cases. Apply the
induction hypothesis to the body and then function extensionality.]

#lean-proof("Evaluation", ("Env.pull_extend", "Term.eval_rename"))

#lemma([Term substitution])[If $sigma in "Sub"_(Sigma)(Gamma,Delta)$ is a typed substitution,
put $eta_(sigma)(v)=E_(I,rho,eta)(sigma(v))$. Then
$
  E_(I,rho,eta)(t[sigma])=E_(I,rho,eta_sigma)(t).
$
*Proof.* Induct on $t$. Variables give the definition of $eta_sigma$; constants
and logical constructors are unchanged. Application follows by the induction
hypotheses. Under abstraction, the lifted substitution fixes zero and weakens
every outer replacement. The renaming lemma gives
$(eta[x])_(sigma^+)=eta_sigma[x]$. Apply the induction hypothesis to the body
for each $x$, then use function extensionality.]

#lean-proof("Evaluation", ("Sub.eval_lift", "Term.eval_substitute"))

#corollary([Beta evaluation])[If $t in "Tm"_(Sigma)(tau :: Gamma,upsilon)$ and
$u in "Tm"_(Sigma)(Gamma,tau)$, then
$
  E_(I,rho,eta)((lambda_tau t)u)
  = E_(I,rho,eta)(t[u]).
$
*Proof.* The left side is $E_(I,rho,eta[E_(I,rho,eta)(u)])(t)$ by evaluation.
The substitution lemma gives the same expression for the right side, because
$eta_([u])$ sends zero to the value of $u$ and each successor to its outer value.]

#lean-proof("Evaluation", ("Sub.eval_single", "Term.eval_beta"))

== Type Instantiation and Choice Coherence

#lemma([Selector coherence])[Identifying the carriers
$D_(rho)(tau[theta])$ and $D_(rho_theta)(tau)$ also identifies their selectors.]

#proof(none)[The type-substitution lemma gives equality of the carrier types in the
metatheory. Substitute this equality in the definition of the selector. Its
nonemptiness argument is a proposition, so proof irrelevance removes any
choice of that argument. The two selector expressions are then the same
function. This proves coherence for equal carriers, not invariance under every
arbitrary bijection between carriers.]

#lean-proof("Instantiation", ("select_heq_of_type_eq", "select_natural"))

#lemma([Type instantiation])[Let $eta$ be an environment for $Gamma[theta]$
at $rho$, and let $eta^theta$ be the environment for $Gamma$ at $rho_theta$
obtained by the carrier identifications above. Then evaluation of $t[theta]$
at $(rho,eta)$ equals evaluation of $t$ at $(rho_theta,eta^theta)$, after
identifying their result carriers.]

#proof(none)[Induct on $t$. Variables use the defining transport in $eta^theta$.
For $c[psi]$, the two valuations agree because
$(rho_theta)_psi=rho_(theta compose psi)$, by type-substitution composition and
its carrier lemma. Application transports the function and its argument, and
abstraction transports an argument before applying the body induction
hypothesis. The propositional constructors preserve their truth operations;
quantifiers transport bound values along the carrier equality. Equality is
unchanged by carrier identification; choice is the selector-coherence lemma.
These are all twelve constructors.]

#lean-proof("Instantiation", ("Env.instPull_extend", "Term.eval_instType"))

In Lean this result is stated using heterogeneous equality `HEq`, since the
two carrier expressions have different indices before identification. The prose
equality always includes this identification; it does not silently compare
values of unrelated types.

== Satisfaction and Validity

An environment satisfies $H$ if every proposition in the list evaluates to a
true proposition. For fixed $Sigma$ and $Gamma$, define $H models_I p$ to mean
that, for every admissible $rho$ and every environment $eta$, satisfaction of
$H$ implies $E_(I,rho,eta)(p)$. This definition includes open sequents.

#lean-def("Rules", ("Valid",))

#lemma([Constant agreement])[Suppose $I$ and $J$ give the same value at every
admissible valuation to every constant occurring in $t$. Then $t$ has the same
value under the two interpretations. If they agree on every constant in $(H,p)$,
then $H models_I p$ if and only if $H models_J p$.]

#proof(none)[Induct on $t$. At a constant occurrence the hypothesis applies at its
induced valuation, not only at the original $rho$. Applications and abstractions
follow from their subterms; variables and logical constructors are independent
of ordinary constants. Apply this equality to each assumption and the conclusion.
The conditions defining validity become identical, in both directions.]

#lean-proof("Transport", ("Term.eval_agree", "valid_transport", "valid_old_language_iff"))

== Congruence of Denotation and Evaluation

The constant-agreement lemma fixes the constructor interpretation $kappa$ and the
valuation $rho$. The next results vary them. Say that $kappa$ and $kappa'$
*agree on* a set $C$ of constructor identifiers when
$kappa(k,n,X_1,...,X_n) = kappa'(k,n,X_1,...,X_n)$ for every $k in C$, every arity
and every tuple of carriers.

#lemma([Type congruence])[If $kappa$ and $kappa'$ agree on $"Cons"(tau)$ then
$D_(kappa,rho)(tau) = D_(kappa',rho)(tau)$. If $rho$ and $rho'$ agree on
$"TVars"(tau)$ then $D_(kappa,rho)(tau) = D_(kappa,rho')(tau)$.]

#proof(none)[Induct on $tau$. A variable uses the hypothesis on $rho$; the base types
and arrows are immediate. For $k(tau_1,...,tau_n)$ the induction hypotheses
identify the argument carriers, so the two sides are $kappa(k,n,dots)$ and
$kappa'(k,n,dots)$ applied to the same tuple, and $k in "Cons"(tau)$.]

#lean-proof("Types", ("Ty.denote_congr_gen", "Ty.denote_congr", "Ty.denote_congr_vars"))

#lemma([Evaluation congruence])[Let $kappa$, $kappa'$ agree on $"Cons"(t)$.
Assume the constants of $t$ are interpreted compatibly: at every instance of a
constant's schema whose constructors lie in $"Cons"(t)$, the values of $I$ under
$kappa$ and of $J$ under $kappa'$ at the pulled-back valuations of one base
valuation are equal, up to the identification of their carriers. Assume the two
environments agree on every variable whose type lies in the agreement region.
Then $E_(I,rho,eta)(t)$ and $E_(J,rho,eta')(t)$ are equal up to the same
identification. For equal $kappa$ it reduces to the constant-agreement lemma.]

#proof(none)[Induct on $t$ through the general statement in which $rho$, $rho'$,
$kappa$, $kappa'$, $I$, $J$ and the environments all vary, with an agreement set
for variables and one for constructors. Variables use the environment hypothesis.
A constant occurrence uses the compatibility hypothesis at its instance; the two
instance valuations agree on the schema variables by type congruence. An
application, an abstraction and a quantifier transport the function, the argument
or the bound value along the carrier equalities supplied by type congruence, using
$"AVars"$ and $"Cons"$ to cover the domain of every binder and the type of every
subterm. Equality and choice transport along one carrier equality. Lean states
all of this with `HEq` since the two carriers are only propositionally equal.]

#lean-proof("Congruence", ("Term.eval_congr", "Term.eval_congr_κ", "Term.eval_congr_vars", "Term.eval_congr_vars_lt"))

#remark([locality of constants])[Dependence of evaluation on type variables alone
is not a property of the term only: a constant's value $I_rho(c)$ may depend on all
of $rho$. `Term.eval_congr_vars` therefore assumes that each constant occurring is
interpreted locally, meaning that $I_rho(c)$ and $I_(rho')(c)$ are equal whenever
$rho$ and $rho'$ agree on $"TVars"(Sigma(c))$. Definitions obtained from a
closed right-hand side are local, which is where type-variable closure is used. The
closure-gate support $"TVars"$ is not enough: $lambda x:alpha_5. "True"$ has empty
$"TVars"$ but its value depends on the carrier of $alpha_5$, which is why the
statement is in terms of $"AVars"$.]

#proposition([Cross-model validity])[Let $kappa$, $kappa'$ be constructor
interpretations that admit the same type valuations, let $(H,p)$ be a sequent, and
let $kappa$, $kappa'$ agree on $"Cons"(H,p)$. If the constants of $(H,p)$ are
interpreted compatibly by $I$ and $J$, then $H models_I p$ if and only if
$H models_J p$. In particular a sequent that does not mention a constructor
identifier $k$ keeps its validity when the carrier of $k$ changes, provided both
interpretations are admissible.]

#proof(none)[Transport the environment from $kappa'$ to $kappa$: variables whose types
lie in the agreement region are cast along the carrier equality, the others (which
no assumption or conclusion can mention) receive an arbitrary inhabitant, which
exists by the nonempty-carrier proposition. Then apply evaluation congruence to
each assumption and to the conclusion. The converse is the same argument with the
roles exchanged. The old-language statements of the previous section are the case
$kappa'=kappa$.]

#lean-proof("Transport", ("valid_transport_κ", "valid_iff_κ", "valid_old_language_iff_κ", "valid_old_language_iff"))
#lean-proof("Definitions", ("valid_definition_old_language_iff_κ", "valid_definition_old_language_iff"))

The admissibility hypothesis is necessary: a constructor interpretation that is not
admissible makes every sequent vacuously valid. The hypothesis that $k$ does not
occur is also necessary. Let $kappa$ send every constructor to a one-point carrier
and $kappa'$ send constructor $0$ to the two-point carrier `Bool`. Then
$forall x,y:0. x = y$ is valid under $kappa$ and not under $kappa'$, while
$forall x,y:1. x = y$ is valid under both, as the proposition predicts.

#lean-proof("TyConCongruence", ("valid_iff_of_tyCon_absent", "valid_allEq_one_unchanged", "valid_allEq_zero_changes"))

These results change only the semantics. The type-definition step that uses them
is the subject of the next section.

== Type-Definition Gate Semantics

This section connects the semantic subtype construction to syntax. A gate allocates
a constructor identifier and two constants of the total signature and changes the
constructor interpretation. It models the semantic content of
`ks_register_type_definition`: the closed predicate over the declared parameters, the
Rep and Abs constants and the three laws. The derivation constructor that makes the
laws derivable in a declaration history, with the freshness of $k$, Rep and Abs with
respect to that history, is introduced in the section on history-indexed extension
derivations; this section proves the semantics it relies on.

#definition([Type-definition gate])[A gate over a signature $Sigma$ consists of

- a constructor identifier $k$ and an arity $n$; the parameters are the type
  variables $alpha_0,...,alpha_(n-1)$, written $bold(alpha)$;
- a representation type $tau$ and a closed predicate
  $P in "Tm"_(Sigma)([], tau -> "bool")$;
- two distinct constant identifiers $r$ (Rep) and $a$ (Abs) with
  $Sigma(r) = k(bold(alpha)) -> tau$ and $Sigma(a) = tau -> k(bold(alpha))$,]

subject to three side conditions: $"AVars"(P) subset.eq {0,...,n-1}$; $k in.not
"Cons"(P)$; and neither $r$ nor $a$ occurs in $P$. The first is the kernel's check
that the type variables of the predicate are parameters. It is stated for $"AVars"$
and not for $"TVars"$ because the kernel counts the domain of every binder, and
because evaluation depends on all annotations (previous section). The second makes
the predicate independent of the carrier being defined, so the definition below is
not circular. The third is local freshness of the new constants.

#lean-def("TypeDefGate", ("TypeDefGate", "paramTy", "TypeDefGate.newTy"))

#definition([Subtype carrier])[For a type $E$ and a predicate $Q$ on $E$ let
$"Sub"(E,Q) = {x in E : Q(x)}$ if $Q$ has a witness and the one-point carrier
otherwise. It is always nonempty. If $Q$ has a witness, $"rep"$ is the projection and
$"abs"$ is the abstraction of the previous section (an element satisfying $Q$ is kept,
any other is sent to a fixed witness); otherwise $"rep"$ is constant. These are
`SubCarrier`, `SubCarrier.rep` and `SubCarrier.abs`, and on the subtype branch they
are `PredicateWitness.rep` and `PredicateWitness.abs`
(`SubCarrier.rep_eq_witness`, `SubCarrier.abs_eq_witness`).]

#lean-def("TypeDefGeneric", ("SubCarrier", "SubCarrier.rep", "SubCarrier.abs"))
#lean-proof("TypeDefGeneric", ("SubCarrier.nonempty", "SubCarrier.abs_rep", "SubCarrier.pred_rep", "SubCarrier.rep_abs", "SubCarrier.rep_eq_witness", "SubCarrier.abs_eq_witness"))

#definition([Model after a type-definition step])[Let $(kappa,I)$ be a model with
$kappa$ admissible. For a tuple of carriers $X = (X_0,...,X_(n-1))$ let $rho_X$ send
$i < n$ to $X_i$ and every other variable to the one-point carrier, and let
$P_X$ be the predicate on $D_(kappa,rho_X)(tau)$ defined by $P_X(x)$ iff
$rho_X$ is admissible and $E_(I,rho_X,[])(P)(x)$ holds. The new constructor
interpretation $kappa'$ agrees with $kappa$ except at $(k,n)$, where
$kappa'(k,n,X) = "Sub"(D_(kappa,rho_X)(tau), P_X)$. The predicate is evaluated in the
old model, so there is no fixed point to solve. The new constant interpretation $I'$
sends $r$ to the Rep of this subtype carrier and $a$ to its Abs, both transported
along the equality $D_(kappa,rho_X)(tau) = D_(kappa',rho)(tau)$ for $rho$ with $rho(i) = X_i$
($i < n$), which holds by type congruence because $"TVars"(tau) subset.eq {0,...,n-1}$ and
$k in.not "Cons"(tau)$. For any other constant $c$ whose schema avoids $k$, $I'(c)$ is
$I(c)$ transported along the equality of the two denotations of its schema; for the
remaining constants $I'(c)$ is a canonical element.]

#lean-def("TypeDefGate", ("TypeDefGate.holds", "TypeDefGate.holdsAny", "TypeDefGate.carrier", "TypeDefGate.newTyCon", "TypeDefGate.repVal", "TypeDefGate.absVal", "TypeDefGate.baseConst", "TypeDefGate.newConst"))
#lean-def("ModelExtension", ("Model", "TypeDefGate.interpret"))

#proposition([Admissibility])[If $kappa$ is admissible, so is $kappa'$.]

#proof(none)[At $(k,n)$ the carrier $"Sub"$ is nonempty whether or not the predicate has a
witness; elsewhere $kappa'=kappa$.]

#lemma([Agreement])[Let $rho$ be admissible for $kappa'$ and let $rho_0$ be the
valuation sending $i < n$ to $rho(i)$ and every other variable to the one-point
carrier. If $I$ is local on the constants of $P$, then for $x$ in $D_(kappa,rho_0)(tau)$,
$P_X(x)$ holds iff $E_(I',rho,[])(P)$ holds of the transport of $x$ to $D_(kappa',rho)(tau)$.]

#proof(none)[Apply evaluation congruence to $P$ under $(kappa',I',rho)$ and $(kappa,I,rho_0)$
with the variable agreement region ${i : i < n}$ and the constructor agreement
region ${j : j != k}$. These cover $"AVars"(P)$ and $"Cons"(P)$ by the first two side
conditions. Every constant $c$ of $P$ is neither $r$ nor $a$ (third condition) and its
instances avoid $k$, so $I'(c)$ is $I(c)$ at the pulled-back valuation of $rho$, and
the two pulled-back valuations of an instance agree on the variables of $Sigma(c)$ by type
congruence. Locality of $I$ on $c$ identifies the two values. The environment is empty.]

#lean-proof("TypeDefGate", ("TypeDefGate.holdsAny_iff", "TypeDefGate.agreeAt_new"))

#theorem([Type-definition laws])[Let $(kappa,I)$ be a model with $kappa$ admissible and
$I$ local on the constants of $P$, and write $(kappa',I')$ for the new model. In
$(kappa',I')$:
$
  tack.r "Abs"("Rep"(x)) = x quad (x : k(bold(alpha))),   P("Rep"(x)) quad (x : k(bold(alpha))),   P(y) tack.r "Rep"("Abs"(y)) = y quad (y : tau)
$
are valid, where the second needs the *witness hypothesis* that $P$ has a witness at every
admissible valuation of the old model: for every $rho$ admissible for $kappa$ there is
$x$ with $E_(I,rho,[])(P)(x)$. The first and third need no witness hypothesis.]

#proof(none)[Let $rho$ be admissible for $kappa'$ and $T = kappa'(k,n,rho|_n)$, which is
$"Sub"(D_(kappa,rho_0)(tau), P_(rho|_n))$ by definition of $kappa'$. The values of the terms
$"Rep"$ and $"Abs"$ at $rho$ are the transports of $"rep"$ and $"abs"$ of this carrier. The first
law is the law $"abs"("rep"(x)) = x$ of the subtype branch if there is a witness; without a
witness $T$ is the one-point carrier and any two elements are equal. The third law
follows from $"rep"("abs"(y)) = y$ for $P_(rho|_n)(y)$, which the Agreement lemma
transfers to the hypothesis $P(y)$; the hypothesis $P(y)$ is itself a witness, so no
further assumption is needed. The second law is the range property of $"rep"$, which holds
on the subtype branch, and the witness hypothesis applied to $rho_0$ shows that this
branch is taken.]

#lean-proof("TypeDefGate", ("TypeDefGate.valid_absRep", "TypeDefGate.valid_repRange", "TypeDefGate.valid_repAbs", "TypeDefGate.repVal_eq_val"))
#lean-proof("ModelExtension", ("TypeDefGate.laws", "TypeDefGate.laws_of_witness_valid"))

#remark([the witness hypothesis])[The kernel requires a hypothesis-free theorem
$tack.r P(w)$ with closed $w$. That derivation yields the witness hypothesis: by
soundness, $P(w)$ is valid in the old model, so $E_(I,rho,[])(P)(w)$ holds for every
admissible $rho$ (`TypeDefGate.witnessAt_of_valid`). The `typedef` derivation constructor
carries a derivation of $P(w)$ at the history preceding the gate, and the soundness
theorem applies its induction hypothesis to it. The hypothesis cannot be dropped: for the gate with representation type `bool`
and predicate $lambda x. "False"$, $P("Rep"(x))$ is not valid in the new model, although the other
two laws are.]

#lean-proof("TypeDefGate", ("TypeDefGate.witnessAt_of_valid",))
#lean-proof("TypeDefExamples", ("trueGate_laws", "falseGate_repRange_not_valid"))

#proposition([Old-language invariance of a type-definition step])[Let the sequent $s$
mention neither $k$ nor the constants $r$ and $a$, and let $I$ be local on the constants of
$s$. Then $s$ is valid in $(kappa',I')$ iff it is valid in $(kappa,I)$. For the canonical
constant interpretation no locality hypothesis is needed.]

#proof(none)[The model pair is cross-model valid (proposition of the congruence
section) once the constants of $s$ are compared at the pulled-back valuations of one base
valuation. For a constant $c$ of $s$, $I'(c)$ is $I(c)$ at the pull-back along
$kappa'$, which differs from the pull-back along $kappa$ in the variables that the schema of $c$ does not
use; those are exactly the variables on which locality asserts independence.]

#lean-proof("TypeDefGate", ("TypeDefGate.valid_iff_old", "TypeDefGate.newTyCon_isAdmissible"))
#lean-proof("ModelExtension", ("ModelExtension.valid_iff", "canonicalConstVal_local", "TypeDefGate.valid_iff_old_canonical"))

#proposition([A type-definition step preserves locality])[If $I$ is local on every
constant, so is $I'$.]

#proof(none)[The new values of $r$ and $a$ depend on $rho$ only through the parameters
$rho|_n$ (the carrier of $k$ at $rho$ and the value of the predicate at $rho_0$ do), and
$"TVars"(Sigma(r)) = "TVars"(Sigma(a)) = {0,...,n-1}$. For the other constants, $I'(c)$ is
either $I(c)$ transported along a type equality, which is local if $I(c)$ is, or a canonical
element of a carrier that depends only on $"TVars"(Sigma(c))$.]

#lean-proof("TypeDefLocal", ("TypeDefGate.repVal_heq", "TypeDefGate.absVal_heq", "TypeDefGate.newConst_local"))

#remark([locality is a model invariant])[Locality is not implied by the type of a constant
interpretation, and it is needed for old-language invariance across a change of $kappa$: two
valuations that differ in a variable the schema of $c$ does not use may be distinguished by a
non-local $I(c)$. The canonical interpretation is local. A definition or specification step
preserves locality only if the right-hand side (resp. predicate) satisfies the annotation
closure $"AVars" subset.eq "TVars"(tau)$; the definition and specification gates state their
closure fields for $"AVars"$, matching the kernel's `term_tyvars`, which counts the domain of
every binder. A type-definition step preserves locality (below). Locality is therefore a
model invariant carried along histories, and old-language invariance holds along a whole
history (section on history-indexed extension derivations).]

= Definitional Extension Discipline (Conservativity Gate)

== Semantic Definition Contract

#definition([Definition gate])[A gate consists of an identifier $c$ and a
closed term $r in "Tm"_(Sigma)([],Sigma(c))$, with
$c$ absent from $r$ and $"AVars"(r) subset.eq "TVars"(Sigma(c))$.
The latter condition records type-variable closure. It is stated for the annotation
support, as the kernel's `term_tyvars` counts the domain of every binder; this makes a
definition step preserve locality of the constant interpretation
(`DefinitionGate.withDefinition_local`). Local freshness here means
absence from the right-hand side; it does not assert absence from a global
history of previous declarations.]

Given an interpretation $I$, define $I^c$ by
$
  (I^c)_(rho)(d) = cases(
    E_(I,rho,eta_0)(r) & "if " d=c,
    I_(rho)(d) & "if " d != c.
  )
$
Here $eta_0$ is the unique environment of the empty context.
The signature is total, so the gate overrides an existing schema slot.

#lean-def("Definitions", ("DefinitionGate", "ConstVal.withDefinition"))
#lean-proof("Definitions", ("DefinitionGate.withDefinition_local",))

#proposition([Defining equation])[The equation $c[iota] =_(Sigma(c)) r$
is valid with empty assumptions under $I^c$.]

#proof(none)[The value of its left side is, by definition, the old value of $r$.
The right side has the same value under $I^c$ as under $I$, since $r$ does not
contain $c$ and the two interpretations agree elsewhere. The constant-agreement
lemma therefore makes the two sides equal at every admissible valuation.]

#lean-proof("Definitions", ("DefinitionGate.rhs_eval_withDefinition", "valid_definition_equation"))

#proposition([Old-language validity])[If $c$ occurs in neither $H$ nor $p$,
then $H models_(I^c) p$ if and only if $H models_I p$.]

#proof(none)[The two interpretations agree on all constants in the sequent. Apply
the constant-agreement lemma in both directions.]

#lean-proof("Definitions", ("valid_definition_old_language_iff",))

This is a semantic statement about a fixed sequent. It neither creates a
`Derivation` of the defining equation nor translates an extended-theory
`Derivation` into a base-theory one. There is no defining-equation admission
constructor among the twelve core rules; the separate object-language infinity
rule is stated below.

== Definition Admissibility Judgment for an Implementation

The intended global admission judgment $"DefOK"(T,c:tau=r)$ additionally
requires that $c$ be absent from committed declaration history and disjoint
from reserved symbols, that $r$ be closed and well-typed at $tau$, and that it
introduce no dependency cycle or undeclared type variable. A scope pop must
not remove a committed definition from this history.

Local shadowing of an ordinary unresolved name does not authorize redefining
an existing committed identifier. A compatible global history must also prevent
a later override from changing a constant on which an earlier defining equation
depends. These history requirements are not fields of `DefinitionGate`.

#proposition([Type-variable closure after instantiation])[If
$"TVars"(r) subset.eq "TVars"(tau)$ (which follows from the gate's $"AVars"$
closure), then
$"TVars"(r[theta]) subset.eq "TVars"(tau[theta])$.]

#proof(none)[Every variable occurring after substitution comes from $theta(i)$
for a variable $i$ that occurred before substitution. The original inclusion
puts each such $i$ in the head type as well. Applying the same substitution
to that type gives the asserted inclusion.]

#lean-proof("Terms", ("Term.typeVars_instType",))
#lean-proof("Definitions", ("DefinitionGate.instType_type_vars_closed",))

A ghost variable occurring only in the body violates the gate. Rejecting it
is a structural restriction, not an assumption that arbitrary historical
definition theorems are accepted safely by the implementation.

= Controlled Specification Extension Discipline

#definition([Specification gate])[Fix an identifier $c$, a type $tau$ with
$Sigma(c)=tau$, a predicate term $P in "Tm"_(Sigma)([tau],"bool")$, and a
closed witness term $w in "Tm"_(Sigma)([],tau)$. Require $c$ to occur in
neither $P$ nor $w$, and require $"AVars"(P) subset.eq "TVars"(tau)$ (the annotation
support, as for definitions).
The witness obligation is a typed derivation $[] tack.r P[w]$.]

The type-variable restriction is a field on the predicate; the current gate
does not contain an additional closure field on $w$. Define the choice term
$v=epsilon_(tau)(lambda_tau P)$. Override the interpretation of $c$ by the value
of $v$, leaving other constants unchanged; call the resulting interpretation
$J$.

#lean-def("Specification", ("SpecificationGate", "specificationTerm", "ConstVal.withSpecification"))
#lean-proof("Specification", ("SpecificationGate.withSpecification_local",))

#proposition([Specification validity])[If $[] tack.r P[w]$, then
$[] models_J P[c[iota]]$.]

#proof(none)[Soundness of the witness derivation (proved independently below) gives
$P[w]$ at every admissible valuation. By the substitution lemma, the value of
$w$ witnesses the interpreted predicate. The semantic choice property implies
that the value of $v$ satisfies this predicate. In $J$, the value of $c$ is
exactly that selected value. Since $P$ does not contain $c$, changing $I$ to
$J$ does not change its interpretation. Another application of the substitution
lemma proves the conclusion.]

#lean-proof("Specification", ("valid_specification", "SpecificationGate.valid_constant_from_typed_derivation"))

#proposition([Old-language validity])[If $c$ is absent from a sequent $(H,p)$,
then $H models_J p$ if and only if $H models_I p$.]

#proof(none)[All constants in the sequent retain their interpretations. The
constant-agreement lemma applies in both directions.]

#lean-proof("Specification", ("SpecificationGate.valid_old_language_iff",))

#contract([Implementation contract (SpecOK)])[A registration procedure must additionally
check global declaration freshness and exact schema agreement. It must justify
the produced theorem $P(c)$ through its explicit extension contract. The
Hilbert-choice rule below is an internal inference rule: it concludes
$P(epsilon P)$ from a derivation of $P(w)$. It is not the `ks_specify_const`
declaration extension, which introduces a fresh constant $c$ and a theorem
$P(c)$ under its witness contract. The current Lean gate proves that the
selected interpretation satisfies $P(c)$, but does not connect the updated
signature and theorem handle to a growing-theory derivation. The exact witness
certificate expected by the MoonBit gate also remains an implementation
boundary (issue #8).]

== Rule Schema: Hilbert Choice from a Witness

Fix a type context $Gamma$ and a type $tau$. Let
$P in "Tm"_(Sigma)(tau :: Gamma,"bool")$ be a predicate body whose first
variable is the distinguished argument, and let
$w in "Tm"_(Sigma)(Gamma,tau)$ be a witness term. Define the choice term in
the ambient context by
$c_P := epsilon_(tau)(lambda_tau P) in "Tm"_(Sigma)(Gamma,tau)$. A derivation with no
propositional assumptions of the substituted witness instance permits the
corresponding choice instance:

$
  frac([] tack.r P[w], [] tack.r P[c_P]).
$

Here $P[w]$ and $P[c_P]$ are capture-avoiding substitutions for the
distinguished variable. The context $Gamma$ is the ambient type context; it is
not a list of propositional assumptions.

#proof([of preservation])[Fix an admissible valuation and an environment for
$Gamma$. The premise supplies an element satisfying the predicate obtained by
extending that environment with the value of $w$. The semantic choice property
then says that the selected element satisfies the same predicate. The choice
term evaluates to that selected element, and the substitution evaluation lemma
identifies this with the displayed conclusion.]

#lean-proof("Rules", ("valid_choose_from_witness",))
#lean-def("Derivation", ("Derivation.chooseWitness",))

This is a witness-based inference rule, not unrestricted axiom admission. Its
conclusion contains the Hilbert-choice term. `ks_specify_const` is a separate
theory-extension operation: it introduces a fresh named constant and registers
the corresponding theorem. The fixed-signature Lean gate models that named
constant by an interpretation override; it is not identified with this rule.

= Global Admissibility and Proof Discipline

The core proof requires an admissible type valuation, an interpretation of every
constant schema, and the recursive evaluator just defined. Carrier nonemptiness,
choice coherence, substitution laws, and primitive-rule preservation are proved
from these definitions. No envelope or interpretation field asserts that
primitive rules are already sound.

The intended implementation must enforce additional admission duties:

1. Accepted theorem handles correspond to justified typed evidence.
2. Named conversions preserve typing and denotation on successful inputs.
3. Definitions, specifications, and type registrations satisfy their stated gates.
4. Theorem reuse preserves declaration identity and compatible provenance.
5. Conversion failures and audit certificates confer no theorem authority.

#block(breakable: false, keyblock("critical", [Issue 15 implementation invariant], [
  Sibling MoonBit `KernelState` histories can allocate the same `ConstId`, so a
  theorem handle records its originating lineage. Admissibility requires that
  lineage to be a prefix of the receiving history; the reported combination of
  `c = T` and `c := F` is rejected before the theorem can be reused. Regression
  tests cover sibling rejection, linear descendants, and witness registration.
  This implementation invariant is separate from the still-required
  MoonBit-to-Lean refinement.
]))

= Primitive Inference Rules

The thirteen constructors collected in this section and the preceding
`SPECIFY` section define the derivation relation. Fix a signature $Sigma$.
Terms in each rule share its displayed type context, except where abstraction
or instantiation changes that context explicitly. Each rule is followed by a
proof that it preserves validity. A hypothesis saying a premise is valid is
only an induction hypothesis for that premise, not an axiom about the whole
calculus.

The mathematical rules act on typed objects and do not return error values.
The rejection notes specify what a named executable interface must check before
constructing the corresponding typed instance. They retain the detailed
engineering side conditions without adding premises to the Lean constructors.

== Rule Schema: `REFL`

Let $t in "Tm"_(Sigma)(Gamma,tau)$. The rule has no theorem premise and produces
$[] tack.r t =_tau t$.

$
  frac(Gamma tack.r_Sigma t:tau, [] tack.r t =_tau t).
$

#proof([of preservation])[Fix an admissible valuation and environment. The
conclusion evaluates to $E(t)=E(t)$, which holds by reflexivity. Empty
assumptions impose no additional condition.]

#lean-proof("Rules", ("valid_refl",))
#lean-def("Derivation", ("Derivation.refl",))

#contract([Interface rejection conditions])[An implementation rejects malformed terms or an equality formed at a different type. Intrinsic typing rules out both inputs before a derivation is constructed.]

== Rule Schema: `ASSUME`

Let $p in "Tm"_(Sigma)(Gamma,"bool")$. The rule introduces exactly the singleton
assumption list $[p]$.

$
  frac(Gamma tack.r_Sigma p:"bool", [p] tack.r p).
$

#proof([of preservation])[An environment satisfying the singleton list satisfies
its member $p$. This is exactly the conclusion's truth condition. The rule is
not permission to assert $p$ without its assumption.]

#lean-proof("Rules", ("valid_assume",))
#lean-def("Derivation", ("Derivation.assume",))

#contract([Interface rejection conditions])[An implementation rejects a non-boolean input. It must preserve the introduced assumption rather than silently return an unconditional theorem.]

== Rule Schema: `ADD_ASSUM`

Given a derivation of $H tack.r p$ and a boolean term $q$, the rule adds $q$ to
the assumption list:

$
  frac(H tack.r p, H ++ [q] tack.r p).
$

#proof([of preservation])[Any environment satisfying $H ++ [q]$ satisfies every
member of $H$. The induction hypothesis therefore yields $p$; the extra
assumption is unused by the conclusion.]

#lean-proof("Rules", ("valid_add_assum",))
#lean-def("Derivation", ("Derivation.addAssum",))

This constructor formalizes kernel `add_assum_checked` (issue #10). The Lean
representation places the new assumption at the head of a list; validity is
invariant under that ordering because hypotheses are interpreted pointwise.

== Rule Schema: `TRANS`

Let $s,t,u$ have the same type $tau$ in $Gamma$. The two premises are
$H tack.r s =_tau t$ and $K tack.r t =_tau u$.

$
  frac(H tack.r s =_tau t quad K tack.r t =_tau u,
       H ++ K tack.r s =_tau u).
$

#proof([of preservation])[Fix an environment satisfying $H ++ K$. It satisfies
each premise list. Premise validity gives
$
  E(s)=E(t), quad E(t)=E(u).
$
Transitivity of equality gives $E(s)=E(u)$, the evaluated conclusion.]

The displayed $t$ is one and the same typed core term. A named boundary may
compare alpha-equivalent presentations only after a justified conversion; it
must not identify differently typed middle terms.

#lean-proof("Rules", ("valid_trans",))
#lean-def("Derivation", ("Derivation.trans",))

#contract([Interface rejection conditions])[Reject a non-equality premise, mismatched middle terms, inconsistent equality types, or a conversion that loses binder-domain types.]

== Rule Schema: `MK_COMB`

Let $f,g$ have type $tau -> upsilon$, and let $u,v$ have type $tau$, all in
$Gamma$. Then

$
  frac(H tack.r f =_(tau -> upsilon) g quad K tack.r u =_tau v,
       H ++ K tack.r f u =_upsilon g v).
$

#proof([of preservation])[An environment satisfying the combined list gives
$E(f)=E(g)$ and $E(u)=E(v)$. Evaluation of application and congruence yield
$
  E(f u)=E(f)(E(u))=E(g)(E(v))=E(g v).
$
Both sides lie in the common codomain $D_(rho)(upsilon)$, so this equality
interprets the well-typed conclusion.]

#lean-proof("Rules", ("valid_mkComb",))
#lean-def("Derivation", ("Derivation.mkComb",))

#contract([Interface rejection conditions])[Reject a non-equality premise, a non-function term in the function position, a domain mismatch, or incompatible codomains. The indexed application constructor makes these constraints explicit.]

== Rule Schema: `ABS`

Let $s,t in "Tm"_(Sigma)(tau :: Gamma,upsilon)$ and let $H$ be an assumption
list in $Gamma$. Apply weakening to each member of $H$, obtaining $"wk"(H)$.

$
  frac("wk"(H) tack.r_(Sigma,tau :: Gamma) s =_upsilon t,
       H tack.r_(Sigma,Gamma) lambda_tau s =_(tau -> upsilon) lambda_tau t).
$

#proof([of preservation])[Fix $rho,eta$ satisfying $H$. For an arbitrary
$x in D_(rho)(tau)$, the renaming lemma shows that $eta[x]$ satisfies $"wk"(H)$:
a weakened old assumption has its old value and does not depend on $x$.
Premise validity therefore gives
$
  E_(I,rho,eta[x])(s)=E_(I,rho,eta[x])(t).
$
This holds for every $x$. Function extensionality and the abstraction evaluation
clause give equality of the two abstractions.]

The named condition “the binder is not free in any assumption” is represented
here by weakening from the outer context. It is not a claim that every premise
list under a binder is suitable for abstraction.

#lean-proof("Rules", ("valid_abs",))
#lean-def("Derivation", ("Derivation.abs",))

#contract([Interface rejection conditions])[Reject a non-variable named binder, a non-equality premise, or an assumption depending on the introduced variable. A named implementation must recover the weakened outer list without capture.]

== Rule Schema: `BETA`

Let $s in "Tm"_(Sigma)(tau :: Gamma,upsilon)$ and
$u in "Tm"_(Sigma)(Gamma,tau)$. The single substitution $[u]$ defined above gives

$
  frac(tau :: Gamma tack.r_Sigma s:upsilon quad Gamma tack.r_Sigma u:tau,
       [] tack.r (lambda_tau s)u =_upsilon s[u]).
$

#proof([of preservation])[The beta evaluation corollary identifies the values
of the redex and its substitution result at every environment. Their equality
therefore holds without hypotheses.]

#note([Scoping principle])[The result is in $"Tm"_(Sigma)(Gamma,upsilon)$ by the
result index of substitution. Beneath a binder, its lift fixes zero and weakens
outer replacements. Thus the contraction cannot manufacture a dangling index
or capture an outer variable in the checked family.]

#lean-proof("Rules", ("valid_beta",))
#lean-def("Derivation", ("Derivation.beta",))

#contract([Interface rejection conditions])[Reject a non-redex, a binder/argument type mismatch, or a failed named reconstruction. An integer-index implementation must additionally establish that its shift-back agrees with the typed single substitution.]

== Rule Schema: `EQ_MP`

Let $p,q$ have type $"bool"$ in $Gamma$. Then

$
  frac(H tack.r p =_("bool") q quad K tack.r p,
       H ++ K tack.r q).
$

#proof([of preservation])[Under satisfaction of $H ++ K$, the first premise
gives equality of the propositions $E(p)$ and $E(q)$; the second gives a proof
of $E(p)$. Transporting that proof along the equality gives $E(q)$.
The rule applies to boolean equality, not to arbitrary equality between values
of another type.]

#lean-proof("Rules", ("valid_eqMp",))
#lean-def("Derivation", ("Derivation.eqMp",))

#contract([Interface rejection conditions])[Reject a non-equality first premise, a mismatch between its left side and the second conclusion, or any non-boolean proposition at those positions.]

== Rule Schema: `DEDUCT_ANTISYM_RULE`

Let $p,q$ be boolean terms, with premises $H tack.r p$ and $K tack.r q$.
Delete every occurrence of $q$ from $H$ and every occurrence of $p$ from $K$.

$
  frac(H tack.r p quad K tack.r q,
       ("del"(H,q)) ++ ("del"(K,p)) tack.r p =_("bool") q).
$

#proof([of preservation])[Fix an environment satisfying the conclusion's
assumptions. To prove $E(p) => E(q)$, suppose $E(p)$ holds. Every member of
$K$ is either structurally $p$, and hence true by this supposition, or remains
in $"del"(K,p)$, and hence is true by the environment hypothesis. The second
premise gives $E(q)$. For the reverse implication, suppose $E(q)$ and restore
$H$ in the same way; the first premise gives $E(p)$. Thus
$
  E(p) <=> E(q).
$
Propositional extensionality turns this equivalence into equality of the two
propositions, which is the interpretation of $p =_("bool") q$.]

No extra equality between $H$ and $K$ is required. If a deletion target was
absent, deletion simply leaves that list unchanged.

#lean-proof("Rules", ("valid_deduct",))
#lean-def("Derivation", ("Derivation.deduct",))

#contract([Interface rejection conditions])[Reject non-boolean conclusions or a malformed hypothesis representation. Absence of the removal target is a valid case, not an alpha-mismatch error. Named normalization must implement the intended removal operation faithfully.]

== Rule Schema: `INST_TYPE`

Let $theta$ be a type substitution. It acts on every member of $H$, on $p$,
and on the shared context. Then

$
  frac(H tack.r_(Sigma,Gamma) p,
       H[theta] tack.r_(Sigma,Gamma[theta]) p[theta]).
$

#proof([of preservation])[Fix an admissible $rho$ and an environment $eta$ for
$Gamma[theta]$ satisfying $H[theta]$. The carrier nonemptiness theorem makes
$rho_theta$ admissible. Pull $eta$ back to $eta^theta$. The type-instantiation
lemma identifies the truth of each instantiated assumption with the truth of
the original assumption at $(rho_theta,eta^theta)$. Apply premise validity
there, then use the same lemma on the conclusion to obtain $E_(I,rho,eta)(p[theta])$.]

All schema occurrences are instantiated by composing substitutions. Choice
coherence is the proved equality-of-carriers lemma, not an additional caller
supplied assertion that this rule is sound.

#lean-proof("Instantiation", ("valid_inst_type",))
#lean-def("Derivation", ("Derivation.instType",))

#contract([Interface rejection conditions])[Reject a mapping whose keys are not type variables or whose images are outside the admitted type language. For wider implementation type constructors, their carrier and substitution laws need separate refinement evidence.]

== Rule Schema: `INST`

Let $sigma in "Sub"_(Sigma)(Gamma,Delta)$ be a typed simultaneous term substitution. Apply it
pointwise to the assumption list and conclusion:

$
  frac(H tack.r_(Sigma,Gamma) p,
       H[sigma] tack.r_(Sigma,Delta) p[sigma]).
$

#proof([of preservation])[Fix $rho,eta$ satisfying $H[sigma]$. Define
$eta_(sigma)(v)=E_(I,rho,eta)(sigma(v))$. The substitution lemma turns satisfaction
of each $h[sigma]$ into satisfaction of $h$ at $eta_sigma$. Premise validity
gives $E_(I,rho,eta_sigma)(p)$. Applying the substitution lemma again identifies
this with $E_(I,rho,eta)(p[sigma])$.]

The substitution has one common target context and preserves the type of each
variable. Its entries are read from the original snapshot; the swap example
is therefore a parallel exchange rather than a sequential rewrite.

#lean-proof("Rules", ("valid_inst_term",))
#lean-def("Derivation", ("Derivation.instTerm",))

#contract([Interface rejection conditions])[Reject a non-variable key, a replacement of the wrong type, or a capture-unsafe conversion. A substitution below a binder must use the lift, not raw name replacement.]

== Rule-Level Constructive Preservation

#proposition([Primitive preservation])[Every instance of one of the thirteen
constructors preserves validity from its premise sequents to its conclusion.]

#proof(none)[Use the corresponding direct argument just given. Reflexivity and
assumption have no theorem premises; `ADD_ASSUM` weakens the assumptions, and
`SPECIFY` uses its witness and the semantic choice property. Transitivity and
application use equality laws; abstraction uses weakening and extensionality; beta uses substitution;
boolean elimination and deduction use proposition equality; the two
instantiation rules use their evaluation lemmas. These arguments depend only
on the type carriers, evaluator, and premise validity.]

The next theorem lifts these thirteen local arguments to every finite typed derivation.



= Soundness Strategy

The main theorem concerns the derivation relation defined by the thirteen rules.
The proof proceeds from constructed semantics to local preservation and then to
induction on a derivation. It does not require a named converter, mutable scope,
or executable theorem handle.

== One-Page Soundness Dependency Map

Each layer below uses the preceding layer. Extension contracts branch from the
soundness and constant-agreement theorems; they do not supply premises back to
primitive soundness.

#align(center)[
  #diagram(
    node((0, 0), [Typed syntax and nonempty carriers]),
    node((0, 1), [Recursive evaluation and substitution lemmas]),
node((0, 2), [Thirteen direct rule-preservation proofs]),
    node((0, 3), [Induction on typed derivations]),
    node((0, 4), [Extension validity and countermodel consequences]),
    edge((0, 0), (0, 1), "->"),
    edge((0, 1), (0, 2), "->"),
    edge((0, 2), (0, 3), "->"),
    edge((0, 3), (0, 4), "->"),
  )
]

In particular, no model contains a field saying “all primitive rules preserve
validity.” Such a field would assume the central obligation instead of proving
it. The selector coherence used in type instantiation is proved independently
from carrier equality.

== Typed Derivations and Inductive Closure

#definition([Derivation])[The judgment $H tack.r_(Sigma,Gamma) p$ holds exactly
when it is generated by the thirteen indexed constructors in the preceding section.
Every premise is itself a derivation of its stated sequent. No leaf admits an
arbitrary boolean term, and no extension-gate node is added to this relation.]

#lean-def("Derivation", ("Derivation",))

#theorem([Soundness])[For every signature $Sigma$, context $Gamma$, constant
interpretation $I$, and derivable sequent $H tack.r_(Sigma,Gamma) p$, the sequent
is valid: $H models_I p$.]

#proof(none)[Induct on the construction of the derivation. In a `REFL` or `ASSUME`
case, the direct preservation proof establishes validity without an induction
hypothesis. In each other case, the induction hypotheses give validity of its
premise derivations. Apply the corresponding preservation proposition to obtain
validity of the conclusion. `ADD_ASSUM` weakens the assumptions, and `SPECIFY`
applies semantic choice to its witness. `ABS` changes the environment by adding an arbitrary
argument; `INST` changes it by evaluating the typed substitution; `INST_TYPE`
changes the valuation and transports the environment. Their evaluation lemmas
justify those changes. There are no further cases.]

#lean-proof("Derivation", ("derivation_sound",))
#lean-proof("Soundness", ("typed_derivation_sound_all", "typed_canonical_derivation_sound"))

The foundational `derivation_sound` declaration takes selector coherence as an
explicit argument. The public package supplies it with `select_natural`, so the
stated theorem for all $I$ has no unproved selector or model-law premise.

== Signature-Generic Non-Triviality

For every signature $Sigma$, the closed typed sentence
$
  (lambda x:"bool". x) =_("bool" -> "bool")
    (lambda x:"bool". x =_"bool" x)
$
is not valid in the standard interpretation of booleans, and hence has no
derivation. Both sides have type `bool -> bool`; the signature contributes no
constant occurrences. Evaluating the alleged equality at `False` would equate
`False` with `True`, which is impossible. Soundness therefore gives
non-derivability for every signature, including every fixed-signature constant
override sequence.

#lean-proof("Concrete", ("signatureGenericFalseSentence_not_valid", "signatureGenericFalseSentence_not_derivable"))
#lean-proof("Soundness", ("typed_signature_generic_consistency", "typed_signature_generic_nonvalid_in_extension"))

== Existence of Interpretations and Non-Triviality

#proposition([Canonical interpretation])[Every signature has a constant
interpretation and hence a model of the checked primitive rules.]

#proof(none)[At each admissible valuation, every principal schema has a nonempty
carrier. Choose one inhabitant for each identifier. This defines the required
family $I_(rho)(c)$. Pair it with the proved selector coherence. Soundness then
shows that every derivation is valid in this interpretation.]

#lean-def("Evaluation", ("canonicalConstVal",))
#lean-proof("Soundness", ("canonicalModel", "typed_model_nonempty"))

This construction models the fixed signature and the primitive calculus. It does
not by itself satisfy every equation an arbitrary later override may request.

#definition([Object-language infinity sentence])[For the distinguished type
`ind`, the infinity sentence is

$
  exists f : "ind" -> "ind".
    (forall x,y : "ind". f(x)=f(y) => x=y)
    and (exists y : "ind". forall x : "ind". f(x)=y => "False").
$]

In the term grammar, negation in the last clause is implication to false. The
sentence is built from the object-language `all`, `ex`, conjunction,
implication, falsity, and equality constructors; it is closed and has type
`bool`.

#theorem([Infinity sentence validity])[For every signature $Sigma$ and every
constant interpretation $I$, the displayed sentence is valid with empty
assumptions.]

#proof(none)[The interpretation of `ind` is $NN$, independently of $I$. Choose
`Nat.succ` for $f$. If $f(x)=f(y)$, injectivity of successor gives $x=y$. For the
non-surjectivity conjunct choose $y=0$; no natural number $x$ satisfies
$succ(x)=0$. The evaluation clauses for the object-language quantifiers,
conjunction, implication, falsity, and equality identify this witness with the
displayed sentence's denotation.]

#lean-def("Infinity", ("indInjectiveBody", "indNonSurjectiveBody", "indInfinitySentence"))
#lean-proof("Evaluation", ("Term.eval_all", "Term.eval_ex", "Term.eval_conj", "Term.eval_imp", "Term.eval_falsity"))
#lean-proof("Infinity", ("indInfinitySentence_valid",))

#contract([Rule (Infinity admission)])[The derivation relation has a premise-free
constructor concluding the displayed sentence. Its soundness case is exactly
the all-model validity theorem above; it does not assume an external
admissibility predicate.]

#lean-def("Derivation", ("Derivation.indInfinity",))
#lean-proof("Derivation", ("derivation_sound",))

The MoonBit `IND_INFINITY_AXIOM` registration (`ks_register_ind_infinity_axiom`)
is an audit marker. It records a hypothesis-free, admissible theorem that mentions
`ind`; it does not check that the theorem states that `ind` is infinite, because
the kernel has no infinity axiom and cannot derive the sentence, so a strict gate
would be unusable. The mathematical statement is established by the Lean rule
above, whose conclusion is valid in every interpretation of the fixed type
grammar; the executable marker is not connected to it (issue #7).

#contract([Implementation refinement contract for connectives and infinity])[The Typed HOL
term grammar treats truth, falsity, conjunction, implication, universal
quantification, and existential quantification as primitive constructors. The
kernel frontend currently builds these connectives as defined constants, and
`IND_INFINITY_AXIOM` builds a term using those definitions. A refinement proof
must therefore provide a translation from each kernel definition to the
corresponding Typed HOL constructor, prove its defining equation is preserved by
lowering, evaluation, substitution, and type instantiation, and show that the
registration lowers to the exact `indInfinitySentence` above, which first
requires a registration that checks that sentence instead of the marker described
above. Merely matching the type of the theorem or finding an occurrence of `ind`
is not enough.
The all-model validity proof depends on the fixed semantic clause
`Ty.ind.denote ρ = Nat`; it does not apply to an arbitrary carrier selected for
`ind`.]

#theorem([Concrete non-derivability])[For the signature assigning identifier
zero type $"ind"$ and identifier one type $"ind" -> "ind"$, the closed
sentence formed by applying the second constant to the first and equating the
result with the first has no derivation with empty assumptions.]

#proof(none)[Interpret the two identifiers by zero and successor, respectively.
Use the type valuation assigning the one-element carrier to every variable,
which is admissible. The displayed sentence evaluates to $1=0$, which is false.
If an empty-assumption derivation existed, soundness would make it true in this
interpretation. This contradiction excludes the derivation.]

#lean-proof("Concrete", ("falseSentence_eval", "falseSentence_not_valid", "falseSentence_not_derivable"))
#lean-proof("Soundness", ("typed_concrete_consistency",))

This theorem is a precise non-triviality witness. A claim about a specific
object-language negation or a complete HOL axiom basis would require its
explicit encoding and corresponding derivations; the theorem name does not
supply those additional claims.

== Finite Semantic Extensions

A semantic extension is a definition override, a specification override, or a
witnessed type-definition contract. Its effect on a constant interpretation is
the corresponding override; the type-definition case is the identity. A
specification extension stores its gate and type equality; its witness is
provided by the history-indexed derivation rule below. Histories are listed
newest first and `interpretSequence` is defined by
$I_([])=I$ and $I_(e :: "es")=I_e(I_("es"))$.

A sequent is _unaffected_ by the list if it mentions none of the identifiers
overridden by a definition or specification in the list. Every sequent is
unaffected by a type-definition step as interpreted here; histories with real
type-definition steps (which change the constructor interpretation) are treated over
model pairs in the section on history-indexed extension derivations.

#lean-def("Conservativity", ("Extension", "Extension.oldLanguage", "Extension.interpret", "interpretSequence", "oldLanguageSequence"))

#theorem([Finite validity conservativity])[If a sequent $(H,p)$ is unaffected
by the finite extension list, then
$
  H models_(I_n) p quad <=> quad H models_(I_0) p.
$]

#proof(none)[Induct on the extension list. For the empty list the interpretations
are equal. For a nonempty list, first apply the one-step agreement theorem to
its head extension, using that the sequent is unaffected by that step. Then
apply the induction hypothesis to the tail, which is also unaffected. The
type-definition case is immediate because its interpretation is unchanged.
Compose the equivalences.]

#lean-proof("Conservativity", ("Extension.valid_iff", "valid_interpretSequence_iff", "typed_global_semantic_conservativity"))

#corollary([Core derivation under an extension interpretation])[Every
base-calculus derivation is valid under $I_("es")$.]

#proof(none)[The history interpretation is still a constant interpretation of the
same signature. Apply the soundness theorem, which holds for every such
interpretation. No extension equation is a new premise of that derivation.]

#lean-proof("Conservativity", ("typed_derivation_sound_in_extension",))
#lean-proof("Soundness", ("typed_extended_derivation_sound",))

#note([Limits of the finite semantic sequence theorem])[This theorem alone does not
check global history freshness or preserve all earlier equations. The
history-indexed derivation rules separately require each modeled constant ID
to be fresh in the preceding extension history and lift old derivations only
when the new step leaves their sequents unchanged. The fixed-signature model
still cannot certify allocation against all implementation declarations. For
example, let two semantic definitions assign the same identifier $c$ two
distinct closed right-hand sides $r$ and $u$, neither containing $c$. Both
local gates can hold, while the second override makes the first equation false
whenever their values differ. Even distinct overridden identifiers can affect
a previous right-hand side that depends on a later-overridden constant. The
theorem protects the unaffected sequent, not all declaration products at once.]

Syntactic conservativity would assert that an extended-language derivation of
an old-language sequent can be reconstructed in the base theory. That requires
a growing theory syntax, explicit admission rules, and a proof transformation.
The current theorem supplies neither that transformation nor a completeness
argument from semantic validity to derivability.

#keyblock("warning", [Exact Extension Claim], [
  History-indexed derivation soundness is proved for definition, witnessed
  specification and witnessed type-definition steps over the fixed type grammar,
  with explicit freshness and old-language side conditions, at the history's model
  pair. The `HistoryDerivation` closure chains the derived type-definition
  products with the supported core rules at that fixed signature. Globally
  compatible growing-signature allocation and derivation erasure (for a type
  definition, a relativisation translation) remain open. The former approximation
  sketches are not referenced as their proofs.
])

== Kernel Extension Mapping and Open Gates

The core kernel rules map to the indexed constructors in `Derivation`; the
complete row-by-row mapping is recorded in
`formal_verification/theory-proof-plan.md`. The extension boundary is:

- `add_assum_checked` maps to `Derivation.addAssum` and its direct preservation
  theorem `valid_add_assum` (issue #10).
- `ks_define_const` and `ks_define_const_thm` map to `DefinitionGate` and
  the `definition` constructor of `ExtensionDerivation`. It admits the defining
  equation at a fresh constant ID in the history, and
  `extension_derivation_sound` proves it under the history interpretation. The
  signature remains fixed. The kernel compares constants by identity: the new
  constant has a fresh identity, and an occurrence of its name that does not denote
  a declared constant is refused as a self-reference (`DefinitionIsCyclic`), which
  matches the gate's freshness condition (issue #9).
- `ks_specify_const` maps to `SpecificationGate` and the witness-based
  `specification` constructor of `ExtensionDerivation`. It requires the witness
  body to be derived at the preceding history, then admits the fresh named
  constant theorem. `Derivation.chooseWitness` remains a distinct Hilbert-choice
  inference rule. The proof does not certify the MoonBit witness representation
  (issue #8).
- `ks_register_type_definition` maps to `TypeDefGate`, its model step
  `TypeDefGate.interpret` and the `typedef` constructor of `ExtensionDerivation`: closed
  predicate over the declared parameters, fresh constructor and Rep/Abs constants, a
  hypothesis-free witness derivation $tack.r P(w)$ at the preceding history, and the three
  laws as derivation conclusions (selector `TypeDefLaw`), valid at the history's model pair.
  History freshness of $k$, Rep and Abs is a carried side condition (unused by the
  semantic soundness induction, but required to form well-formed histories);
  the carrier-level `TypeDefContract` is the family obtained at the old model. The kernel's
  string-name lowering and the MoonBit gate itself are not verified.
- `ks_ind_infinity_axiom` maps mathematically to `Derivation.indInfinity`,
  whose conclusion is the explicitly encoded `indInfinitySentence`. Its
  soundness case uses `indInfinitySentence_valid`, proved for every
  interpretation because `ind` denotes `Nat` in every admissible type
  valuation. The executable kernel's anchor gate and construction of this exact
  sentence remain unverified (issue #7).

The kernel has no eta inference primitive. A future extension rule must be
added to the typed judgment and receive its own semantic preservation case.

== History-Indexed Extension Derivations

A history $"es"$ is listed newest declaration first and consists of declaration steps
(`ModelExtension`): a definition, a specification or a type definition. A type-definition
step changes the constructor interpretation, so histories are interpreted over model pairs
$M=(kappa,I)$ (`Model`, with $kappa$ admissible): $M_([])=M$ and
$M_(e :: "es")=e(M_("es"))$, where a definition or specification step overrides a constant and
keeps $kappa$, and a type-definition step is the model step of the type-definition gate.
(The earlier `Extension` and `interpretSequence` are indexed by one fixed $kappa$ and remain
for the type-definition-free finite statement above.) For each step the constants and
constructor identifiers it introduces are `ModelExtension.constantIds` and
`ModelExtension.tyConIds`; `modelHistoryIds(es)` and `modelHistoryTyCons(es)` collect the
identifiers already used in a history. A sequent is in the old language of a step if it
mentions none of the constants and none of the type constructors the step introduces.

Write $"ExtDerivation"("es",H,p)$ for the history-indexed judgment. Every core derivation is
available at every history; an old derivation can be lifted across a new step only when the
sequent is in the old language of that step:

$
  frac("Derivation"_S (H,p), "ExtDerivation"("es",H,p))
  quad
  frac("ExtDerivation"("es",H,p) quad e."oldLanguage"(H,p), "ExtDerivation"(e :: "es",H,p)).
$

A fresh definition adds its defining equation. A specification step must carry a derivation
of its witness body at the preceding history, so the theorem's proof dependency is reflected
in the index. A type definition carries, in the same way, the witness derivation of the
kernel's hypothesis-free theorem $tack.r P(w)$, and one constructor with a three-valued
selector $l$ concludes the law it names (`TypeDefLaw`):
$l = "absRep"$ gives $tack.r "Abs"("Rep"(a)) = a$, $l = "repRange"$ gives
$tack.r P("Rep"(a))$, and $l = "repAbs"$ gives $P(r) tack.r "Rep"("Abs"(r)) = r$. Write
$e_D$, $e_G$ and $e_T$ for the definition, specification and type-definition steps:

$
  frac(D : "DefinitionGate"(S) quad D."id" in.not "modelHistoryIds"("es"),
    "ExtDerivation"(e_D :: "es",[],c_D = "rhs"_D)).
$

$
  frac("ExtDerivation"("es",[],"body"_G) quad G : "SpecificationExtension"(S) \ G."gate"."id" in.not "modelHistoryIds"("es"),
    "ExtDerivation"(e_G :: "es",[],P_G (c_G))).
$

$
  frac("ExtDerivation"("es",[],P(w)) quad T : "TypeDefGate"(S) \ k in.not "modelHistoryTyCons"("es") quad ("rep", "abs") in.not "modelHistoryIds"("es"),
    "ExtDerivation"(e_T :: "es", "ctx"(l), "law"(l))).
$

The soundness theorem is stated at the history's model pair: if the base model $M$ is local
(every constant interpreted locally; the canonical models are), then every derivation at
$"es"$ is valid in $M_("es")$, constructor interpretation included.

#lemma([Every step preserves locality])[If $M$ is local so is $e(M)$.]

#proof(none)[A definition or specification step overrides one constant by the value of a term
whose annotation support lies in the type variables of that constant's schema (the
$"AVars"$ closure of the gates), so by `Term.eval_congr_vars` the new value depends only
on those variables. A type-definition step is the preceding proposition.]

#lean-proof("Definitions", ("DefinitionGate.withDefinition_local",))
#lean-proof("Specification", ("SpecificationGate.withSpecification_local",))
#lean-proof("ModelExtension", ("Model.IsLocal", "ModelExtension.interpret_isLocal", "interpretModels_isLocal"))

#theorem([Old-language invariance along a history])[Let $M$ be local and let a sequent
$(H,p)$ be in the old language of every step of $"es"$. Then $H models_(M_("es")) p$ if and
only if $H models_M p$. Over the canonical model of an admissible $kappa$ no locality
hypothesis remains.]

#proof(none)[Induct on $"es"$, applying the one-step theorem to the head step in the model of
the tail: old-language invariance of definition and specification steps, and the
type-definition proposition above, whose locality premise holds by the previous lemma.]

#lean-def("ModelExtension", ("ModelExtension", "ModelExtension.interpret", "interpretModels", "modelHistoryIds", "modelHistoryTyCons", "oldLanguageModels", "Model.canonical", "Model.default"))
#lean-proof("ModelExtension", ("valid_interpretModels_iff", "typed_global_semantic_conservativity_models"))

#theorem([Soundness of history-indexed derivations])[If $M$ is local, every derivation
$"ExtDerivation"("es",H,p)$ satisfies $H models_(M_("es")) p$.]

#proof(none)[By induction on the derivation. The core case invokes `derivation_sound` in the
final model pair. The lifting case uses the old-language theorem for the newly added step,
with its locality hypothesis supplied by the locality lemma. Definition uses the locally
proved equation in the model of the preceding history. Specification first applies the
induction hypothesis to its witness derivation and then the witness-based gate theorem. For
a type definition the induction hypothesis for the witness derivation gives $P(w)$ valid in
$M_("es")$, so the predicate has a witness at every admissible valuation
(`TypeDefGate.witnessAt_of_valid`); the type-definition laws theorem then validates the
selected law in the model after the step. The predicate's constants are local by the
locality lemma.]

#lean-def("ExtensionDerivation", ("TypeDefLaw", "TypeDefLaw.ctx", "TypeDefLaw.sequent", "ExtensionDerivation"))
#lean-proof("ExtensionDerivation", ("TypeDefGate.valid_law", "extension_derivation_sound", "typed_extension_derivation_sound", "typed_extension_derivation_sound_default"))

The `HistoryDerivation` relation embeds these introduction products and closes
the same fixed-signature history under all supported core rules. In particular,
its `abs`, `trans`, `mkComb`, `eqMp`, `deduct`, instantiation and witness-choice
constructors can consume a derived extension theorem. Its soundness is proved at
the history's model pair, and the unit example composes a type-definition law
through `abs`.

#lean-def("HistoryDerivation", ("HistoryDerivation",))
#lean-proof("HistoryDerivation", ("history_derivation_sound", "typed_history_derivation_sound", "history_derivation_old_language_valid", "history_generic_false_not_derivable"))
#lean-proof("HistoryDerivationExamples", ("unit_absRep_function_valid", "unit_history_composition_nonvacuous"))

#corollary([Derivation-level conservativity])[A sequent in the old language of every step of
$"es"$ that is derivable at $"es"$ is valid in the canonical base model.]

#lean-proof("ExtensionDerivation", ("extension_derivation_old_language_valid",))

`HistoryDerivation` also has a structural rule that replaces the hypotheses of a derived
sequent by any list containing them, because hypotheses are a set; the kernel compares them
logically.

#theorem([Definition erasure])[Let $D$ be a definition gate with identifier $c$ and
right-hand side $r$, and let $U_D$ replace every occurrence $c_sigma$ of $c$ by the
instantiated definition $r[sigma]$. If $s$ is derivable at the history $D :: "es"$, then
$U_D s$ is derivable at $"es"$. Consequently a sequent that does not mention $c$ and is
derivable at $D :: "es"$ is derivable, unchanged, at $"es"$.]

The proof is by induction on the derivation. Replacement commutes with renaming,
substitution and type instantiation; the last needs the functor laws of type instantiation
on closed terms, which are proved through an annotation-preserving erasure to untyped terms.
The defining equation becomes reflexivity of $r$ because $c$ does not occur in $r$. 

#lean-proof("Unfold", ("HistoryDerivation.erase_definition", "HistoryDerivation.definition_conservative"))
#lean-proof("TermLaws", ("Term.instType_var", "Term.instType_instType"))

#theorem([Specification erasure])[Let $E$ be a specification extension of the constant $c$
with predicate $P$, and let $U_E$ replace every occurrence $c_sigma$ by the choice term
$epsilon (lambda x. P[sigma])$. If $s$ is derivable at the history $E :: "es"$, then $U_E s$
is derivable at $"es"$; a sequent not mentioning $c$ is derivable unchanged.]

The specification step carries a derivation of $P(w)$ at $"es"$. Under $U_E$ the step's
theorem $P(c)$ becomes $P(epsilon P)$, which is the `chooseWitness` rule applied to that
derivation, because $c$ occurs neither in $P$ nor in $w$. Compatibility with type
instantiation holds because the replacement is the instantiation of a closed term. Erasure
of type definitions is not proved here.

#lean-proof("SpecErasure", ("HistoryDerivation.erase_specification", "HistoryDerivation.specification_conservative"))

The freshness premises of the three introduction clauses serve a separate well-formedness
condition: they require each declared constant identifier, and for a type definition the
constructor identifier, to be absent from the earlier history. The induction proving
`extension_derivation_sound` does not use these premises. Its definition case uses
`valid_definition_equation`, whose proof uses the local condition `DefinitionGate.fresh`.
Its specification case uses `SpecificationExtension.valid_gate`, whose proof uses
`SpecificationGate.fresh`. Its type-definition case uses the gate fields (`k_fresh`,
`rep_fresh`, `abs_fresh`), which keep the predicate independent of the new constructor and
constants. Thus local non-self-reference is part of product soundness, while history
uniqueness is a judgment side condition; this theorem alone does not prove global
consistency or preservation of every prior declaration equation. The side condition of the
lifting clause is necessary: dropping the clause for the type-definition step makes
the old-language invariance of that step, on which the lifting case relies, unprovable
(the sentence $forall x,y:k. x = y$ is valid or not depending on the carrier of $k$).

#example(none)[Over a signature with $"Rep" : k -> "bool"$ and $"Abs" : "bool" -> k$, let
$P = lambda x:"bool". x = "True"$, so that $k$ is a one-element type. The witness derivation
$tack.r P("True")$ at the empty history uses `beta`, `refl` and the derived symmetry step
(`Derivation.of_eq_left`). The three laws are then derivation conclusions at the history
$[e_T]$, hence valid at its model pair; the old-language theorem $tack.r "True" = "True"$
lifts across the step with the lifting clause and is valid at the canonical base model; and
the generic false sentence is not valid at the extended model pair, so non-triviality
survives the type definition.]

#lean-def("TypeDefDerivationExamples", ("unitGate", "unitHistory", "unitModel"))
#lean-proof("TypeDefDerivationExamples", ("Derivation.of_eq_left", "unitGate_witness_derivation", "unit_absRep_derivation", "unit_repRange_derivation", "unit_repAbs_derivation", "unit_laws_valid", "unit_old_language_derivation", "unit_old_language_valid", "unit_model_nontrivial", "typed_signature_generic_nonvalid_in_history"))

In this specification, the word `SPECIFY` can denote the internal Hilbert
choice inference only when explicitly qualified as the witness rule. It is
distinct from `ks_specify_const`, the declaration extension that introduces a
fresh named constant. The Lean judgments are `Derivation.chooseWitness` for
the former and `ExtensionDerivation.specification` for the latter.

#lean-def("Conservativity", ("Extension", "interpretSequence", "extensionHistoryIds"))

#note([Limits])[The judgment composes definition, specification and type-definition proofs through
finite histories over one fixed total `Signature`, and `HistoryDerivation` closes those
products under the supported core rules. This remains a fixed-signature construction:
growing-signature syntax, globally compatible allocation, syntactic conservativity and
erasure to a growing-signature core derivation are not claimed. A type-definition erasure
would need a relativisation translation (the new type has no definable replacement in the
base grammar), and semantic validity does not imply derivability. The kernel's string names,
the reservation of builtin constructor names and the MoonBit gate are outside this model.]

== Type Preservation for Application Congruence

#proposition(none)[The `MK_COMB` conclusion is a boolean term in the same context as
its premises.]

#proof(none)[If $f,g:tau -> upsilon$ and $u,v:tau$, then application formation gives
$f u,g v:upsilon$. Equality formation at $upsilon$ therefore gives
$f u =_upsilon g v:"bool"$. The context is unchanged in both constructions.
This is a typing argument; its semantic preservation was proved separately
in the rule section.]

#lean-def("Terms", ("Term.app", "Term.equal"))
#lean-def("Derivation", ("Derivation.mkComb",))

== Public Proof Package and Trust Basis

`TypedHOLCoreProofPackage` collects the checked core, semantic extension
lemmas, and countermodels. Its public theorem is
`QEDFV.HOL.typed_hol_core_proof_complete`. The word “complete” names the
assembled core proof package; it does not claim completeness of HOL or a full
growing-theory calculus.

#lean-def("Soundness", ("TypedHOLCoreProofPackage", "typedHOLCoreProofPackage"))
#lean-proof("Soundness", ("typed_hol_core_proof_complete",))

The audited public results depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The retained development adds no custom axiom and contains no
`sorry` or `admit`. This trust basis is explicit: the proofs are carried out in
Lean's classical metatheory and checked by its kernel.

= Part II: Engineering Realization (Informative + Conformance)

This part is intentionally downstream of Part I. It records one concrete realization strategy
and executable conformance hooks, but does not redefine logic.

== Engineering Correspondence

The formal clauses above map to implementation modules as follows.

- `src/kernel/types.mbt`: type constructors, decomposers, predicates, and type-level operators.
- `src/kernel/terms.mbt`: term constructors, decomposers, typing helper, and term-level operators.
- `src/kernel/thm.mbt`: theorem abstraction and primitive rule implementation.
- `src/kernel/sig.mbt`: scoped signature stack, constant registration, and definitional signature operations.

This mapping is informative: it supports coverage review and does not alter any Part I definition or theorem.

Concrete representation details: the reserved `@` identity is seeded into the initial signature for lookup while insertion of reserved names is rejected. `Thm` stores typed De Bruijn assumptions and conclusion; named `Term` values are reconstructed at the public boundary. The Part I statements about logical reservation and named presentation refer to semantic roles, not literal storage layout.

== Audit Certificates and Replay Interface

#definition([Minimal Extension Certificate])[
For each successful admissible extension gate step, the kernel appends one audit certificate:
$
  "ExtCert" ::= ("gate", "heads", "witness_digest")
$
where:

- `"gate" in {"DefOK", "TypeDefOK", "SpecOK"}`
- `"heads"` is the finite list of newly admitted symbol heads for that step
- `"witness_digest"` is a stable theorem digest string for audit replay/indexing.]

#contract([Constraint (Audit-Only Semantics)])[
Extension certificates are observability artifacts only. They are never accepted as a runtime proof
that bypasses any admissibility gate or theorem-admissibility check.]

#definition([Admissible Theorem at State])[
$
  "Admissible"(T, t_h)
$
means that the handle has a justified sequent in the interpretation determined
by the compatible declaration history $T$. Primitive evidence must translate to
the typed derivation relation; extension-produced evidence needs its separate
semantic contract. This is a conformance target, not the current executable
`thm_is_admissible` predicate and not a completed MoonBit refinement theorem.]

#definition([Sentence in Base Language])[
$
  "SentenceInLanguage"(T_0, t_h)
$
means: the theorem conclusion of $t_h$ is a closed boolean sentence and every non-reserved
symbol in it belongs to the language of $T_0$.]

#definition([Executable Old-Language Replay Check])[
Given base state $T_0$, extended state $T_1$, and theorem $t_h$, define:
$
  "ConservativeReplayOK"(T_0, T_1, t_h) := \
  "Admissible"(T_1, t_h) and "SentenceInLanguage"(T_0, t_h) \
  and "Admissible"(T_0, t_h)
$
This is an intended regression proxy. The executable checks cannot be equated
with derivability or semantic validity without a refinement proof; issue #15
shows that provenance can remain unsafe despite structural admissibility.]

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

== Conformance Obligations (Part I -> Part II)

The following obligations define what counts as a faithful implementation of Part I:

1. *Rule fidelity*: each exported theorem-constructor path must correspond to one Part I primitive rule schema with identical side conditions.
2. *Boundary fidelity*: named/De Bruijn conversion functions must satisfy the Part I alpha/typing/denotation bridge lemmas on all successful inputs.
3. *Scope fidelity*: push/pop/shadowing behavior must preserve resolved-theorem stability exactly as stated in Part I scope theorems.
4. *Gate fidelity*: all extension admissions must be checked against Part I gate judgments (`DefOK`, `TypeDefOK`, `SpecOK`) without hidden implementation-only bypasses.
5. *Certificate non-authority*: audit certificates may index/replay checks but never serve as proof objects that bypass gate or rule checking.

The current `ks_specify_const` path checks a closed witness application and then creates the theorem `P(c)` inside the trusted kernel extension path. The Typed HOL development proves its stated semantic validity contract. A
syntactic admission trace and the concrete MoonBit refinement remain obligations;
this path must not be identified with a base-calculus primitive derivation.

Conformance failure in any item above is treated as an implementation defect, not as a change to the logic.

== Conformance Transfer Principle

#definition([Faithful realization])[A realization is faithful if each accepted
primitive trace translates to a typed derivation with the same sequent, each
extension product satisfies its semantic contract in a compatible history, and
the boundary conversions preserve denotation. Certificates carry no evidence
of their own.]

#proposition([Transfer under a refinement])[Suppose a realization is faithful.
If it accepts a primitive-only theorem handle translated to $(H,p)$, then
$H models_I p$ in the corresponding interpretation $I$. For an accepted
extension product, the same conclusion requires the realized extension contract.]

#proof(none)[In the primitive case, the refinement supplies a `Derivation`, and
soundness supplies validity. Boundary preservation transfers that validity to
the presented statement. In the extension case, use its validity contract and
history-compatibility invariant, then the same boundary preservation. Dropping
an audit certificate does not change any justification.]

This is a mathematical consequence of explicitly stated refinement hypotheses.
No retained Lean theorem supplies the MoonBit-to-Lean translation or the history
invariant. A concrete transfer proof remains an implementation task.

== Design Delta vs HOL Light

QED and HOL Light share the LCF principle and primitive-rule trust model, but QED currently differs in two engineering choices:

1. Rule execution layer:
  HOL Light executes directly over named terms; QED executes rule cores over De Bruijn objects and lifts results to named boundaries.
2. Constant signature policy:
  HOL Light uses globally unique constant naming; QED currently uses scoped signature stacks with explicit shadowing.

These deltas are intentional and must be read as implementation-level policy choices, not changes to the object-logic proposition/equality calculus.

== Lawful Axiomatic Type Classes via Dictionary Passing (Refinement Blueprint)

#keyblock("warning", [Design Blueprint; Not a Lean-Checked Frontend], [
  The detailed dictionary-passing design is retained as a future engineering
  profile. Its named predicates and judgments are definitions of that profile;
  its preservation, coherence, and resolution statements are proof obligations.
  No current Typed HOL theorem implements dictionary resolution or allocates
  the wider `list`/`int` type constructors used in examples. Object-language
  connectives in this blueprint require explicit definitions and derived rules.
])

Within this subsection, write $cal(I)$ for the frontend instance environment
(`Instances` in prose) and `Scopes` for name lookup. They are distinct from the semantic constant
interpretation $I$ and fixed signature $Sigma$ of Part I. Prerequisite lists are
written $Xi$; they do not replace the typed context $Gamma$. In law-encoding
examples, displayed quantifiers and implications denote the intended encoded
object-language connectives. Their definitions and derived rules are obligations
of this profile, whereas implications between judgments are metatheoretic.

This subsection records one refinement strategy for constrained generic reasoning in STT/HOL, without adding primitive kernel rules. The strategy follows three principles:

1. class signatures + laws are encoded as higher-order boolean predicates,
2. generic proofs carry class constraints as explicit assumptions/antecedents,
3. concrete instances discharge those constraints by ordinary primitive instantiation + elimination rules.

#definition([Law Predicate Encoding])[
For a class with one operation field, elaboration introduces a predicate over that operation. For semigroups:
$
  "IsSemigroup" : "fun"("fun"(alpha, "fun"(alpha, alpha)), "bool")
$
$
  "IsSemigroup"(op) = forall x : alpha. forall y : alpha. forall z : alpha.
  op(op(x)(y))(z) = op(x)(op(y)(z))
$
Admissibility is checked by the same definitional gate as other constants: fresh head, typed rhs, and no ghost type variables (`TVars` side condition in `DefOK`).]

#definition([Constrained Generic Theorem Shape])[
Generic theorem schemas are represented with explicit constraints:
$
  tack.r "IsSemigroup"(d) arrow.r.double "GenericBody"(d, u_1, ..., u_n)
$
The corresponding assumption-list presentation is:
$
  ["IsSemigroup"(d)] tack.r "GenericBody"(d, u_1, ..., u_n)
$
The equivalence between implication-style and assumption-style presentations is treated as an explicit derived-rule obligation over Part I primitives (not as parser sugar).]

#definition([Frontend Instance Environment])[
Dictionary resolution is performed against a dedicated instance environment $"Instances"$, separate from the scoped constant stack $"Scopes"$.]

#definition([Instance Record Shape])[
An instance entry is represented as:
$
  i ::= ("cls", kappa_"cls", "ty", nu, "dict_schema", d_"gen", "reqs", Xi, "owner", M_"def", "vis", V)
$
where:

- $kappa_"cls"$ is the class head identity;
- $nu$ is a normalized target type expression;
- $d_"gen"$ is the polymorphic dictionary schema term for this entry;
- $Xi$ is a finite list of prerequisite class constraints (superclass/dependent constraints);
- $M_"def"$ is the defining module identity;
- $V$ is the visibility policy payload.]

#definition([Type Normalization and Instance Key])[
Type normalization used by resolution keys is:
$
  "NormTy" : "Type" -> "Type"
$
and instance keys are:
$
  "InstKey"(kappa_"cls", tau) := (kappa_"cls", "NormTy"(tau))
$]

#note([Clarification (Role of `InstKey`)])[
`"InstKey"` is an indexing/caching artifact for frontend lookup acceleration. Logical
instance selection is defined by schema matching (`"Match"`), not by key equality alone.]

#note([Scope Restriction (Single-Parameter Class Profile)])[
This realization profile supports only unary class heads and one target type argument per instance key.
Multi-parameter classes are out of scope for this section and require separate coherence machinery (for example functional dependencies or equivalent constraints).]

#definition([Type Equivalence Domain for Resolution])[
Write:
$
  tau_1 equiv_"ty" tau_2
$
iff $tau_1$ and $tau_2$ are alpha-equivalent as simple types (same constructor tree, possibly different type-variable names).
In the frontend type representation (`TyVal`/`TyApp`), there is no type-level beta/eta reduction; therefore key normalization is alpha-canonicalization, not higher-order type reduction.]

Canonical clauses for normalization:
$
  "NormTy"("TyVal"(a_i)) = "TyVal"(v_"idx"(a_i))
$
$
  "NormTy"("TyApp"(k, [tau_1, ..., tau_n]))
  = "TyApp"(k, ["NormTy"(tau_1), ..., "NormTy"(tau_n)])
$
where $"idx"$ maps each variable to first-occurrence order in a deterministic left-to-right traversal.

#definition([Parser Variable Stability for `NormTy`])[
For any input type $tau$, let $"VarOrder"(tau)$ be the list of first occurrences of type variables produced by:]

1. depth-first traversal of the type syntax tree,
2. left-to-right visit order of constructor arguments,
3. recording only first occurrence of each variable.

Let $"Ren"_tau$ map the $j$-th variable in $"VarOrder"(tau)$ to $"TyVal"(v_j)$.
Normalization is then:
$
  "NormTy"(tau) := "TyRename"("Ren"_tau, tau)
$

Determinism/alpha-reflection clauses:
$
  tau_1 equiv_"ty" tau_2 arrow.r.double "VarOrder"(tau_1) and "VarOrder"(tau_2)
  " induce alpha-equivalent normalized outputs"
$
so variable naming choices from parser/elaboration cannot change resolution outcomes.

#contract([Obligation (Normalization Stability under Type Equivalence)])[
Resolution conformance requires:
$
  tau_1 equiv_"ty" tau_2 arrow.r.double "NormTy"(tau_1) = "NormTy"(tau_2)
$
and conversely:
$
  "NormTy"(tau_1) = "NormTy"(tau_2) arrow.r.double tau_1 equiv_"ty" tau_2
$]

#definition([Instance Environment Carrier])[
The environment is a class-indexed finite instance store:
$
  cal(I) : "ClassHead" arrow.r "FinSet"("InstRec")
$
with invariant:
$
  i in cal(I)(kappa_"cls") arrow.r.double "ClassOf"(i) = kappa_"cls"
$]

#definition([Type-Size Metric for Termination Checks])[
$
  "TySize"("TyVal"(a)) = 1
$
$
  "TySize"("TyApp"(k, [tau_1, ..., tau_n]))
  = 1 + "TySize"(tau_1) + ... + "TySize"(tau_n)
$]

#definition([Well-Formed Instance Environment])[
Write:
$
  cal(I) tack.r "wf_I"
$
iff all conditions hold:]

1. *Finite store*: total entry set $"Entries"(cal(I))$ is finite.
2. *Schema normalization*: for each $i in "Entries"(cal(I))$,
   $
     "TyOf"(i) = "NormTy"("TyOf"(i))
   $
3. *Class/index coherence*: if $i in cal(I)(kappa_"cls")$ then $"ClassOf"(i) = kappa_"cls"$.
4. *Schema witness*: let $Gamma_i$ contain the prerequisite dictionary
   placeholders, and let $A_i$ list their law propositions. Each entry must
   provide a well-typed schema in $Gamma_i$ and a replayable witness
   $
     A_i tack.r "LawPred"("ClassOf"(i))("DictSchema"(i)).
   $
   A closed interface theorem is obtained only after explicitly abstracting the
   placeholder parameters and encoding these assumptions as antecedents. It is
   not an unconditional closed law theorem for an open schema.
5. *No overlap by unification*: for each class head $kappa_"cls"$ and distinct
   $i_1, i_2 in cal(I)(kappa_"cls")$:
   $
     not "Unifiable"("TyOf"(i_1), "TyOf"(i_2))
   $
6. *No orphan*: for each entry $i$ in module $"OwnerMod"(i)$,
   $
     "OwnerMod"(i) = "OwnerClass"("ClassOf"(i))
     " or " \
     "OwnerMod"(i) = "OwnerTyHead"("TypeHead"("TyOf"(i)))
   $
7. *Paterson-style decrease on prerequisites*: for each $i in "Entries"(cal(I))$ and
   each $(kappa_r, nu_r) in "Reqs"(i)$:
   $
     "TySize"(nu_r) < "TySize"("TyOf"(i))
     " and "
     "TVars"(nu_r) subset.eq "TVars"("TyOf"(i))
   $
8. *Prerequisite-key uniqueness*: for each entry $i$, normalized keys induced by $"Reqs"(i)$ are pairwise distinct.
9. *Type-variable containment in prerequisites*:
   $
     "TVars"("Reqs"(i)) subset.eq "TVars"("TyOf"(i))
   $
   so prerequisite constraints cannot introduce unconstrained escaping type variables.

#definition([Module Resolution Context])[
Resolution context is:
$
  Delta ::= ("mod", M_"cur", "visible", V_"cur")
$
with visibility predicate:
$
  "Visible"(Delta, i) := "OwnerMod"(i) in "VisibleMods"(Delta)
$]

#definition([Instance Admission Step])[
Instance admission is a frontend state transition:
$
  cal(I) ; M tack.r "add_inst"(kappa_"cls", nu, d_"gen", Xi, V) mapsto cal(I)'
$
admissible only if:]

1. $nu = "NormTy"(nu)$;
2. for each $i in cal(I)(kappa_"cls")$, $"Unifiable"("TyOf"(i), nu)$ is false;
3. orphan side condition above holds for module $M$;
4. $"TVars"(Xi) subset.eq "TVars"(nu)$;
5. $"WitnessStratified"(cal(I), (kappa_"cls", nu), i_"new")$;
6. for each $(kappa_r, nu_r) in Xi$, $"TySize"(nu_r) < "TySize"(nu)$;
7. $cal(I)' = "InsertInst"(cal(I), kappa_"cls", i_"new")$;
8. $cal(I)' tack.r "wf_I"$.

#definition([Global Resolution Coherence])[
Define auxiliary predicates:

$
  "ResOut"(cal(I), Delta, kappa_"cls", tau, d)
  := (cal(I) ; Delta tack.r "Resolve"(kappa_"cls", tau) mapsto d)
$
$
  "CanonEq"(d_1, d_2)
  := ("CanonDict"(d_1) = "CanonDict"(d_2))
$
For a fixed environment, resolution context, class, and target type,
$"ResUnique"(cal(I), Delta, kappa_"cls", tau)$ means that whenever
$
  "ResOut"(cal(I), Delta, kappa_"cls", tau, d_1), quad
  "ResOut"(cal(I), Delta, kappa_"cls", tau, d_2),
$
the outputs satisfy $"CanonEq"(d_1,d_2)$.]

Then global coherence is:
$
  "Coherent"(cal(I))
  := forall Delta. forall kappa_"cls". forall tau.
     "ResUnique"(cal(I), Delta, kappa_"cls", tau)
$

#contract([Design proof obligation (Add-Instance Preservation)])[
Suppose $cal(I)$ is well formed and coherent, and the stated instance admission
step produces $cal(I)'$. Then $cal(I)'$ should also be well formed and coherent.
Well-formedness follows from the admission check. Preservation of coherence is
a separate obligation; it does not follow merely by naming that check.]

#definition([Witness Stratification])[
For candidate key $k$ and candidate entry $i$, write:
$
  "WitnessStratified"(cal(I), k, i)
$
iff there exists a finite replay trace $"Pi"_w$ such that:]

1. $"ReplayPartI"("Pi"_w)$ produces the schema witness $A_i tack.r "LawPred"("ClassOf"(i))("DictSchema"(i))$ in $Gamma_i$;
2. $k in.not "ResolveKeys"("Pi"_w)$ (the witness trace does not resolve the key being admitted);
3. $"ResolveKeys"("Pi"_w) subset.eq "EntryKeys"(cal(I))$ (all resolution dependencies are in the old environment).

#definition([Resolution Judgment])[
Implicit dictionary search is modeled as:
$
  cal(I) ; Delta tack.r "Resolve"(kappa_"cls", tau) mapsto d
$
Define the following premise shorthands:

$
  "NoFeedbackSubst"(theta, tau)
  := "TVars"("TySubstRange"(theta)) subset.eq "TVars"("NormTy"(tau))
$
The predicate $"TyMatch"(i,tau,theta)$ holds when all three conditions hold:]

1. $"Dom"(theta) subset.eq "TVars"("TyOf"(i))$;
2. $"TySubst"(theta,"TyOf"(i)) = "NormTy"(tau)$;
3. $"NoFeedbackSubst"(theta,tau)$.

$
  "Match"(cal(I), kappa_"cls", tau, i, theta)
  := (i in cal(I)(kappa_"cls") and "TyMatch"(i, tau, theta))
$
$
  "ReqInst"(i, theta)
  := "TySubstReqs"(theta, "Reqs"(i))
$
$
  "ReqDecrease"(i, theta, tau)
  := forall (kappa_r, tau_r) in "ReqInst"(i, theta).
     "TySize"(tau_r) < "TySize"(tau)
$
$
  "ReqOK"(cal(I), Delta, i, theta, d_s)
  := "ResolveReqs"(cal(I), Delta, "ReqInst"(i, theta)) mapsto d_s
$
The predicate $"BuildOK"(i,theta,d_s,d)$ records three successful checks:

1. $d = "CanonDict"("BuildDict"(i,theta,d_s))$;
2. $"CoreTypeOK"(d,"TySubst"(theta,"DictTy"(i)))$;
3. $"ReplayLawOK"(i,theta,d_s,d)$.

These are acceptance conditions. A proof that the construction passes them must
start from schema typing and prerequisite witnesses, rather than assume
$"BuildOK"$ itself.

#definition([Dictionary Calculus for Instance Realization])[
Each instance stores a polymorphic schema term $"DictSchema"(i) = d_"gen"$ with
prerequisite dictionary placeholders $[v_1, ..., v_n]$ corresponding to $"Reqs"(i)$.
Dictionary construction is:
Let $sigma_d$ map the prerequisite placeholders $v_j$ to the corresponding
resolved dictionaries $d_j$. Define
$
  "BuildDict"(i,theta,d_s)
  := "TermSubst"(sigma_d,"TySubstTerm"(theta,d_"gen")).
$
The substitution is capture avoiding and must respect the placeholder types.]

This enforces a two-stage realization discipline:

1. instantiate type parameters by $theta$ on the dictionary schema;
2. fill prerequisite dictionary placeholders by resolved dictionaries.

#definition([Core Typing Contract for Dictionary Terms])[
$
  "CoreTypeOK"(d, tau) := ("empty" tack.r.r d : tau)
$]

#definition([Dictionary Canonicalization Policy])[
$
  "CanonDict" : "RTerm" -> "RTerm"
$
is a deterministic frontend alpha-canonicalization operator on resolved dictionary terms
(stable binder renaming + stable constructor ordering; no semantic rewriting rule beyond alpha-normalization).
No new Part I equality principle is introduced by this policy.]

#definition([Deterministic Prerequisite Resolution])[
Prerequisites are resolved over the declared order in $"Reqs"(i)$:
$
  "ResolveReqs"(cal(I), Delta, []) mapsto []
$
For a nonempty prerequisite list, suppose its head is $r=(kappa,tau)$.
Resolve the head to $d_r$ and the tail $Xi$ to $d_s$. The result is then
$
  "ResolveReqs"(cal(I),Delta,"Cons"(r,Xi))
  mapsto "Cons"(d_r,d_s).
$
An implementation may keep a set of active keys during recursion; revisiting
an active key yields `PrereqCycle`.]

#note([Resolution success clause])[Suppose the environment is well formed and an
entry $i$ and matching substitution $theta$ satisfy the following conditions:]

1. $"Match"(cal(I),kappa_"cls",tau,i,theta)$ and $"Visible"(Delta,i)$;
2. $"ReqDecrease"(i,theta,tau)$;
3. $"ReqOK"(cal(I),Delta,i,theta,d_s)$;
4. $"BuildOK"(i,theta,d_s,d)$.

The resolution judgment then holds:
$
  cal(I);Delta tack.r "Resolve"(kappa_"cls",tau) mapsto d.
$
The decrease check applies to *instantiated* prerequisite types. A smaller raw
schema need not remain smaller after substitution. Thus the raw schema-size
admission check alone does not prove resolution termination.

#contract([Design proof obligation (Match coherence)])[In a well-formed environment,
if both $"Match"(cal(I),kappa_"cls",tau,i_1,theta_1)$ and
$"Match"(cal(I),kappa_"cls",tau,i_2,theta_2)$ hold, then $i_1=i_2$.
The intended proof uses the non-unifiability condition: two distinct schemas
matching a common target would have a common instance. Variables of different
schemas must first be renamed apart. This establishes schema uniqueness;
canonical dictionary uniqueness additionally requires the construction below.]

#contract([Design proof obligation (Dictionary realization)])[Suppose the stored schema
is well typed in its prerequisite-placeholder context and has a replayable law
witness in that context. Suppose $theta$ matches the target and each dictionary
in $d_s$ has the corresponding instantiated prerequisite type and law witness.
Set $d="CanonDict"("BuildDict"(i,theta,d_s))$. The construction must establish
$
  "CoreTypeOK"(d,"TySubst"(theta,"DictTy"(i)))
$
and $"ReplayLawOK"(i,theta,d_s,d)$. The intended argument applies type
instantiation, followed by typed capture-avoiding term substitution, to the
schema and its witness, discharges the instantiated law assumptions using the
prerequisite witnesses and explicit derived rules, then uses the
alpha-preservation contract of $"CanonDict"$. These hypotheses are obligations on admitted schema records;
the existing Typed HOL library has not yet formalized this frontend profile.]

#definition([Replay Obligation for Nested Dictionary Terms])[
$"ReplayLawOK"(i, theta, d_s, d)$ holds iff elaboration emits a finite replay trace $"Pi"$ such that:]

1. $"Pi"$ is a sequence of Part I-admissible primitive-rule steps plus admissible gate references;
2. replay of $"Pi"$ derives:
   $
     tack.r "LawPred"("ClassOf"(i))(d)
   $
3. every non-variable subterm constructor appearing in $d$ is either:
  - a constant admitted by Part I definitional/specification/type gates, or
  - a dictionary obtained from recursive prerequisite resolution in $d_s$.

This condition prevents "frontend-only valid" nested dictionary constructions that lack Part I replay witnesses.

#definition([Logical Solvability Predicate])[
Write:
$
  "Solvable"(cal(I), Delta, kappa_"cls", tau)
$
iff there exist $i, theta$ such that:
$
  "Match"(cal(I), kappa_"cls", tau, i, theta) and "Visible"(Delta, i)
$
and $"ReqDecrease"(i,theta,tau)$ holds,
and every prerequisite pair $r in "ReqInst"(i, theta)$ is recursively solvable under the same $(cal(I), Delta)$.
The recursion is interpreted using the instantiated strict decrease included
in this definition, rather than the raw schema metric alone.]

#contract([Design proof obligation (Resolution Completeness on the Admissible Profile)])[
Assume the admitted schemas satisfy the dictionary-realization obligation.
For a well-formed environment, every solvable target should have a successful
resolution. The proposed proof is induction on the size of the target type.
The explicit decrease condition permits induction for every prerequisite;
dictionary realization then supplies the final construction and law replay.]

#contract([Design proof obligation (Resolution soundness to solvability)])[
Every successful resolution should imply solvability. Induct on its finite
resolution tree. Its success checks give a visible matching schema and a strict
decrease; the induction hypotheses give solvability of its prerequisites.]

#definition([Substitution Opacity / No-Feedback])[
The substitution witness $theta$ used by `"Match"` and `"BuildDict"` is existential and
resolution-local: it is not exported to callers and does not refine/modify the caller type environment.
At matching time this is enforced syntactically by $"NoFeedbackSubst"(theta, tau)$.]

The operational boundary contract is that resolution leaves the caller's
context and existing terms unchanged. If the caller supplies a judgment
$Gamma tack.r_Sigma t:tau$, that same judgment remains available after resolution.
This is a state-preservation requirement, not a new inference rule that derives
the supplied judgment again. A realization must prove the absence of writes to
the caller's typing state.

#definition([Resolution Failure Classification])[
Resolution failure codes are:
$
  "ResolveError" ::= & "NoInstance"        && " key not found" \
                   | & "InvisibleInstance" && " key found but not visible" \
                   | & "AmbiguousInstance" && " malformed environment violates uniqueness" \
                   | & "PrereqCycle"       && " recursive prerequisite cycle" \
                   | & "PrereqFailure"     && " prerequisite resolution failed"
$]

Layer-separation constraints for $"Scopes"$ and $"Instances"$:

- $"Scopes"$ controls local name lookup/shadowing for ordinary terms only;
- $"Instances"$ controls implicit instance resolution only;
- push/pop on $"Scopes"$ does not mutate $"Instances"$;
- theorem-object acceptance in Part I never reads $"Instances"$ directly.

#definition([Instance Witness Obligation])[
Each concrete instance provides a closed law witness:
$
  tack.r "IsSemigroup"("IntAdd")
$]

#note([Admissibility Policy (Coherence-Oriented Baseline)])[
The baseline realization profile used for conformance adopts:]

1. *No local instances*: local scope mutation cannot introduce or remove implicit instances.
2. *No overlap under matching*: for one class head, two distinct instance schemas must not be unifiable.
3. *No orphan*: an instance declaration in module $"M"$ is admissible only if $"M"$ owns the class head or the target type head.
4. *Fail on ambiguity*: if uniqueness cannot be established, elaboration fails and no theorem object is produced.

#note([Refinement Pipeline (No New Kernel Rules)])[
Given a generic derivation and witness theorem:]

1. apply `INST_TYPE` to specialize type variables (e.g. $alpha := "int"$),
2. apply `INST` to replace the dictionary variable (e.g. $d := "IntAdd"$),
3. discharge the class antecedent using the witness theorem via an explicit Part I derived rule for implication elimination (constructed from `EQ_MP` or an equivalent `DEDUCT_ANTISYM_RULE` path).

Resulting instance theorem shape:
$
  tack.r "GenericBody"("IntAdd", u_1, ..., u_n)
$

#definition([Trait-Trace Erasure Function])[
Elaboration traces with trait-resolution events are erased by:
$
  "EraseTraitTrace" : "TraitTrace" -> "PartITrace"
$
with clauses:]

1. dictionary-resolution events map to explicit `INST_TYPE`/`INST` substitutions with resolved dictionary terms;
2. prerequisite-resolution events map to earlier substitutions in dependency order;
3. law-discharge events map to explicit derived implication-elimination subtraces over Part I primitives;
4. frontend bookkeeping-only events map to empty trace segments.

#contract([Design proof obligation (Erasure Faithfulness for Trait Elaboration)])[
$
  ("TraitAccept"(cal(I), Delta, "Pi"_tr, s))
  /
  ("ReplayPartI"("EraseTraitTrace"("Pi"_tr)) mapsto (tack.r s))
$]

#note([Meta-Theory Targets (Part II Conformance)])[
The following properties are required for this refinement profile:

- *Resolution Uniqueness*: if $cal(I) ; Delta tack.r "Resolve"(kappa_"cls", tau) mapsto d_1$ and
  $cal(I) ; Delta tack.r "Resolve"(kappa_"cls", tau) mapsto d_2$, then
  $
    "CanonDict"(d_1) = "CanonDict"(d_2)
  $
  (hence $d_1 equiv_alpha d_2$).
- *Normalization Stability*: type-equivalent targets cannot diverge by normalization (`NormTy` respects and reflects $equiv_"ty"$).
- *Resolution Termination*: recursive superclass/instance search must terminate on admissible instance graphs.
- *Prerequisite Determinism*: ordered `"ResolveReqs"` evaluation yields one dictionary vector for each prerequisite list.
- *Type-Variable Discipline*: prerequisite constraints satisfy $"TVars"(Xi) subset.eq "TVars"(tau)$ and do not escape admission context.
- *Witness Stratification*: instance-law witnesses are provable from the old environment and cannot self-justify the to-be-admitted key.
- *Resolution Completeness on Solvable Inputs*: every logically solvable visible key resolves successfully.
- *Scope Insensitivity*: resolution outcomes are invariant under push/pop mutations of $"Scopes"$ that do not alter $"Instances"$.
- *Elaboration Erasure to Part I*: every accepted constrained elaboration trace erases to a derivation tree using only Part I primitive rules and admissible gate steps.]

#note([Boundary Clarification (LCF Discipline)])[
Resolution algorithms, candidate search order, and module visibility checks belong to frontend metatheory. Kernel trust remains unchanged: acceptance depends only on explicit dictionaryized terms and replayable Part I derivation traces.]

#note([Clarification (Syntactic vs Extensional Dictionary Equality)])[
In this profile, automatic resolution guarantees canonical syntactic representatives through `"CanonDict"`.
Manually supplied dictionaries that are extensionally equal but syntactically different are not identified by extra kernel extensionality principles.
This is a usability/coherence policy choice, not a kernel soundness risk.]

#note([Conservative Status Note])[
Under the obligations above, this refinement is conservative with respect to Part I:

- no new primitive inference rule is introduced,
- all class-law usage is explicit in assumptions/antecedents,
- all debt discharge is replayable as Part I primitive-rule traces.]

#keyblock("info", [Error Semantics Status], [
  Kernel gate/rule entrypoints use typed error channels (`LogicError` for theorem rules and `SigError` for theory/state admissions). The remaining option-style helpers are internal normalization/lookup utilities and are not trusted external admission interfaces.
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
- `DEDUCT_ANTISYM_RULE`: non-propositional premise -> `NotBoolTerm`;
  absence of a removal target is not an error. A malformed normalized list
  violates the representation contract.
- `INST_TYPE` and `INST`: invalid substitution shape -> `InvalidInstantiation`; capture-risk boundary -> `VariableCaptured`; post-substitution typing failure -> `TypeMismatch`.

This mapping is a conformance target for engineering realizations and gives a direct bridge from Part I failure clauses to machine-checkable error constructors.

= Maintenance and Further Refinement

The mathematical argument and the Lean development must evolve together. A
change to a type, term constructor, or primitive rule requires updating its
formation clauses, evaluation lemmas, preservation proof, and derivation case.
A new extension must state whether its result is a semantic validity theorem or
a syntactic derivability theorem, and supply the corresponding argument.

The remaining implementation work includes named-boundary refinement, compatible
declaration history, theorem provenance, and justified extension admission.
Dictionary passing and richer frontend facilities remain design profiles.
Audit certificates may expose evidence but may not substitute for it.

#keyblock("info", [Established Results], [
  The checked core has nonempty carriers, a coherent selector, recursive
  evaluation, substitution laws, preservation of all thirteen derivation rules, and
  derivation soundness. Definition and specification overrides preserve validity
  of unaffected sequents; witnessed subtypes satisfy the Abs/Rep laws. The
  concrete natural-number interpretation provides a non-derivability witness.
  Each result is proved in the text and annotated with its Typed HOL Lean location.
])

#set heading(numbering: none)

= Appendix A: Primitive Rule Dependency Matrix

The table separates the mathematical preservation argument from named-interface
validation. All proof names below are in `QEDFV.HOL`; constructor definitions
are in `Derivation.lean`.

#table(
  columns: (1fr, 1.6fr, 1.3fr), inset: 5pt,
  table.header([*Rule*], [*Mathematical dependency*], [*Lean preservation theorem*]),
  [REFL], [Reflexivity in the carrier], [`Rules.valid_refl`],
  [ASSUME], [Satisfaction of singleton list], [`Rules.valid_assume`],
  [ADD_ASSUM], [Weakening the assumption list], [`Rules.valid_add_assum`],
  [TRANS], [Premise-list satisfaction and transitivity], [`Rules.valid_trans`],
  [MK_COMB], [Application congruence at matching types], [`Rules.valid_mkComb`],
  [ABS], [Weakening evaluation and function extensionality], [`Rules.valid_abs`],
  [BETA], [Typed single-substitution evaluation], [`Rules.valid_beta`],
  [EQ_MP], [Transport along proposition equality], [`Rules.valid_eqMp`],
  [DEDUCT], [Exact list deletion and propositional extensionality], [`Rules.valid_deduct`],
  [INST_TYPE], [Carrier transport, selector coherence, evaluation], [`Instantiation.valid_inst_type`],
  [INST], [Simultaneous substitution evaluation], [`Rules.valid_inst_term`],
  [CHOOSE\_#linebreak()WITNESS], [Witness substitution and the selector property], [`Rules.valid_choose_from_witness`],
  [INFINITY], [Validity of the explicit sentence, witnessed by successor], [`indInfinitySentence_valid`],
  table.hline(stroke: 0.6pt + ink),
)

`CHOOSE_WITNESS` is Hilbert's internal choice inference from an already derived
instance. It is distinct from `ks_specify_const`, which adds a fresh named
constant through a history-indexed extension derivation.

Here `Rules` and `Instantiation` indicate source modules, not extra namespace
components in the Lean declaration name. A theorem such as `valid_abs` is named
`QEDFV.HOL.valid_abs`.

Named matching, conversion failure, and declaration-history checks must refine
these typed constraints. They are not additional assumptions in the preservation
proofs themselves.

= Appendix B: Closure Checklist

This checklist distinguishes checked mathematics from implementation duties.
It is a review index, not an independent proof.

#note([Checked Typed HOL mathematics])[]

1. Types have exactly the four stated constructors and nonempty carriers.
2. Every term has a context and result-type index; constants record schema instances.
3. Renaming and substitution lift beneath binders without capture.
4. Type substitution composes and commutes with carrier interpretation.
5. Evaluation of terms commutes with renaming, term substitution, and type instantiation.
6. Equality denotes actual carrier equality; the selector property and coherence are proved.
7. Sequents use finite assumption lists; deletion removes every exact matching term.
8. Every derivation constructor has a direct case in `derivation_sound`, including
   `Derivation.indInfinity` and `indInfinitySentence_valid`.
9. Derivation soundness follows by induction without a model field assuming it.
10. A canonical interpretation exists, and a concrete false sentence is not derivable.
11. Definition and specification overrides validate their products under the stated gates.
12. Old-language validity is invariant under finite unaffected override sequences.
13. Witnessed subtype families satisfy nonemptiness and the three Abs/Rep laws.

#contract([Implementation and wider-theory obligations])[]

1. Named conversions must preserve alpha-equivalence, typing, and denotation.
2. Name lookup must preserve frozen identities across scope mutation.
3. Theorem reuse must enforce compatible declaration lineage; the issue #15
   MoonBit invariant is implemented and regression-tested.
4. Global admission must enforce freshness and preserve previous declaration commitments.
5. Type-constructor registration must integrate carrier and type-substitution semantics.
6. Extension products require explicit justification beyond the thirteen derivation constructors.
7. A syntactic conservativity claim needs a genuine growing-theory derivation transformation.
8. Audit certificates must remain non-authoritative.
9. Dictionary resolution, laws, coherence, and termination remain design proof obligations.
10. A checked MoonBit refinement is required before transferring core soundness to the executable kernel.

= Appendix C: Definition and State Soundness Validation Scenarios

These scenarios retain the detailed implementation review plan. They are
expected behaviors, not claims of Lean-checked MoonBit conformance. The proof
annotations in Part I identify the mathematical results available for each case.


Validation scenarios for definition-layer completeness:

1. *Ghost-Type Rejection Scenario*:
  attempt $"def" c : "bool" = r(alpha)$ with $alpha in.not "TVars"("bool")$;
  expected result: rejected by `TVars(r) subset.eq TVars(tau)`.
2. *Instantiation Coherence Scenario*:
  from an admissible definition theorem $tack.r c = r$, apply $"INST_TYPE"$ on head variables;
  expected result: instantiated head/body remain coherent as one definitional instance.
3. *Shadowing Separation Scenario*:
  local scope shadowing of ordinary constants is permitted;
  definitional head reuse is rejected by global freshness in $"DefOK"$.
4. *Old-Language Conservativity Scenario*:
  for a sequent excluding the overridden identifier, validity is unchanged
  under the old and new interpretations. Reconstructing an old-theory
  derivation is a separate syntactic conservativity target.
5. *Pop-Then-Redefine Rejection Scenario*:
  define head $c$, pop local scope, attempt defining $c$ again;
  expected result: rejected because $c in "DefHeads"(T)$ despite local lookup removal.

These scenarios organize validation of the definition and state interfaces;
passing them would not replace a universal refinement proof.

= Appendix D: Type Soundness Validation Scenarios

These scenarios retain the detailed implementation review plan. They are
expected behaviors, not claims of Lean-checked MoonBit conformance. The proof
annotations in Part I identify the mathematical results available for each case.


Validation scenarios for type-extension completeness:

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
  define $id$ at principal schema $"fun"(alpha, alpha)$, then use it at $"fun"("bool", "bool")$ and $"fun"("ind", "ind")$;
  expected result: both uses are accepted via the instance relation $tau prec.eq tau_"gen"$, without requiring per-type renamed constants.

These scenarios organize type-registration validation. The current Lean
carrier theorem covers the fixed type grammar and the separate subtype contract.

= Appendix E: Typed De Bruijn Core Validation Scenarios

These scenarios retain the detailed implementation review plan. They are
expected behaviors, not claims of Lean-checked MoonBit conformance. The proof
annotations in Part I identify the mathematical results available for each case.


Validation scenarios for typed-core/boundary consistency:

1. *Binder-Type Distinction Scenario*:
  compare $lambda (x:tau_1). x$ and $lambda (x:tau_2). x$ with $tau_1 eq.not tau_2$;
  expected result: lowered typed De Bruijn abstractions are distinct ($"DAbs"(tau_1, ...) eq.not "DAbs"(tau_2, ...)$).
2. *TRANS Middle-Term Guard Scenario*:
  chain two equalities whose middle terms are structurally similar but differ in binder-domain type labels;
  expected result: TRANS rejects by typed-core mismatch.
3. *BETA Binder Agreement Scenario*:
  attempt beta contraction with argument type not equal to abstraction binder-domain label;
  expected result: rejected before contraction.
4. *Boundary Lift Type Coherence Scenario*:
  lower and lift a theorem involving typed abstractions;
  expected result: reconstructed theorem preserves abstraction-domain types and cannot cross-type-identify abstractions.

These scenarios check the named implementation boundary against the intrinsic
core typing constraints. Its concrete conversion proof remains separate.

= Appendix F: Specification and Choice Validation Scenarios

These scenarios retain the detailed implementation review plan. They are
expected behaviors, not claims of Lean-checked MoonBit conformance. The proof
annotations in Part I identify the mathematical results available for each case.


Validation scenarios for derived specification-admission discipline:

1. *Empty-Hypothesis Witness Requirement Scenario*:
  provide a witness theorem with non-empty assumptions for specification introduction;
  expected result: rejected by `SpecOK` witness-shape policy.
2. *Freshness Collision Scenario*:
  attempt to introduce specification constant $c$ where $c$ is reserved or already present in theory history;
  expected result: rejected by specification freshness constraints.
3. *Type-Schema Widening Scenario*:
  attempt specification admission where the admission procedure widens schema beyond $"Gen"(tau)$;
  expected result: rejected by strict type-schema lock.
4. *Derived-Path Integrity Scenario*:
  attempt to admit specification constant without explicit Choice + `DefOK` derivation trace;
  expected target behavior: the product carries its checked admission
  justification; reconstruction through an explicit choice axiom and definition
  is one future syntactic route, not a theorem of the current thirteen-rule calculus.
5. *Old-Language Conservativity Scenario*:
  after admissible specification extension, prove a sentence not mentioning the new symbol;
  expected semantic result: validity is unchanged for the unaffected sequent;
  syntactic reconstruction remains an additional refinement obligation.

These scenarios organize review of specification admission. The semantic
validity proof in Part I does not construct a base-calculus admission trace.

= Appendix G: Part II Conformance Validation Scenarios

These scenarios retain the detailed implementation review plan. They are
expected behaviors, not claims of Lean-checked MoonBit conformance. The proof
annotations in Part I identify the mathematical results available for each case.


Validation scenarios for faithful realization transfer from Part II into Part I:

1. *Rule-Fidelity Replay Scenario*:
  replay each exported theorem-constructor trace as a sequence of Part I primitive rule instances;
  expected result: one-to-one replay succeeds without introducing extra rule premises.
2. *Boundary-Fidelity Scenario*:
  for accepted conversions, check alpha/typing/denotation bridge lemmas against Part I boundary requirements;
  expected result: accepted conversions satisfy all three bridges; rejected conversions produce no theorem.
3. *Scope-Fidelity Stability Scenario*:
  perform push/add/pop mutations after theorem construction and replay the same theorem object;
  expected result: resolved-theorem premises/conclusion remain invariant exactly as Part I stability theorem states.
4. *Gate-Fidelity Scenario*:
  attempt to admit extensions via any path not passing `DefOK`/`TypeDefOK`/`SpecOK`;
  expected result: admission rejected and no theorem object produced.
5. *Certificate Non-Authority Scenario*:
  supply valid-looking extension certificate metadata without matching admissibility derivation;
  expected result: no theorem acceptance; certificates are observability only.
6. *Lawful Dictionary Instantiation Scenario*:
  construct one constrained generic theorem schema plus one closed instance witness, then replay the instance proof via `INST_TYPE`, `INST`, and antecedent discharge;
  expected result: final concrete theorem is accepted with no residual class-law assumption, and replay uses only Part I primitive-rule obligations.
7. *No-Orphan Admission Scenario*:
  declare an instance in module $"M"$ where $"M"$ owns neither the class head nor the target type head;
  expected result: admission rejected before theorem construction.
8. *Overlap Rejection Scenario*:
  attempt to admit two schemas for one class head that are unifiable (for example $"Eq"(alpha)$ and $"Eq"("int")$);
  expected result: second admission rejected and resolution remains unique.
9. *Scope-Shadowing Invariance Scenario*:
  run dictionary resolution before and after local push/add/pop shadowing operations over `Scopes` while keeping `Instances` unchanged;
  expected result: identical resolved dictionary (up to alpha-equivalence) and identical replayable theorem trace.
10. *Normalization Completeness Scenario*:
  query resolution with two alpha-equivalent target types $tau_1 equiv_"ty" tau_2$ that differ only by type-variable naming;
  expected result: matching succeeds for both targets with equivalent substitutions (via `"NormTy"` invariance), and resolution returns alpha-equivalent canonical dictionaries.
11. *Nested Dictionary Replay Scenario*:
  construct an instance whose dictionary is built from prerequisite dictionaries and auxiliary admitted constants;
  expected result: `"BuildOK"` holds only when `"CoreTypeOK"` and `"ReplayLawOK"` both hold, and replay yields a Part I law theorem for the built dictionary term.
12. *Witness Self-Cycle Rejection Scenario*:
  attempt to admit key $k$ with a witness trace that resolves $k$ itself;
  expected result: `"WitnessStratified"` fails and admission is rejected.
13. *Solvable-Implies-Resolvable Scenario*:
  build a visible acyclic prerequisite chain satisfying $"Solvable"(cal(I), Delta, kappa_"cls", tau)$;
  expected result: resolution succeeds and returns some dictionary term $d$.
14. *Polymorphic-Match Scenario*:
  register one schema instance with head $"Eq"("list"(alpha))$ and query resolution at $"Eq"("list"("int"))$;
  expected result: `"Match"` succeeds with some type substitution $theta$ and the resolved dictionary is well-typed at the instantiated dictionary type.
15. *Add-Instance Coherence Preservation Scenario*:
  start from coherent $cal(I)$, admit one new instance through `"add_inst"` that satisfies non-overlap/orphan/Paterson side conditions, then replay prior and new resolutions;
  expected result: resulting environment remains `"wf_I"` and `"Coherent"`, and previously resolvable queries keep the same canonical dictionaries.
16. *No-Feedback Resolution Scenario*:
  run resolution for a constrained goal under a fixed typing context $Gamma$, then continue typing unrelated terms;
  expected result: generated matching substitution $theta$ is not exported, and typing facts in $Gamma$ are unchanged.
17. *Parser Variable Stability Scenario*:
  resolve the same goal twice with alpha-renamed parser-level type variables in target annotations;
  expected result: `"VarOrder"` + `"NormTy"` yield alpha-equivalent normalized targets, and resolution returns the same canonical dictionary.

These seventeen scenarios retain the broader frontend validation profile.
They do not certify resolution completeness or a concrete implementation transfer.

= Appendix H: Claim-to-Proof Trace Matrix

Each row names the exact checked result and its source module. The namespace is
`QEDFV.HOL`; module names are source locations. Requirements below the table
have no retained approximation theorem standing in for their proof.

Kernel primitive names follow the checked MoonBit entry points:
`refl_checked` maps to `Derivation.refl`; `assume_checked` to
`Derivation.assume`; `add_assum_checked` to `Derivation.addAssum`;
`trans_checked` to `Derivation.trans`; `mk_comb_rule_checked` to
`Derivation.mkComb`; `abs_rule_checked` to `Derivation.abs`;
`beta_rule_checked` to `Derivation.beta`; `eq_mp_checked` to
`Derivation.eqMp`; `deduct_antisym_rule_checked` to `Derivation.deduct`;
`inst_type` to `Derivation.instType`; and `inst_checked` to
`Derivation.instTerm`. Each constructor is covered by the corresponding case
of `derivation_sound`. Extension operations are mapped separately above because
their current Lean results are semantic contracts, not evolving-theory
derivations.

#context {
  set text(size: 9.3pt)
  show raw: set text(size: 8pt)
  table(
  columns: (0.7fr, 1.5fr, 2.2fr), inset: 5pt,
  table.header([*Claim*], [*Mathematical result*], [*Lean source and declaration*]),
  [C1], [Nonempty carriers], [`Types.lean`: `Ty.carrier_nonempty`],
  [C2], [Renaming and substitution evaluation], [`Evaluation.lean`: `Term.eval_rename`, `Term.eval_substitute`],
  [C3], [Beta evaluation], [`Evaluation.lean`: `Term.eval_beta`],
  [C4], [Selector and type-instantiation coherence], [`Instantiation.lean`: `select_natural`, `Term.eval_instType`],
  [C5], [All primitive derivations are valid], [`Derivation.lean`: `derivation_sound`],
  [C6], [Definition equation and old-language validity], [`Definitions.lean`: `valid_definition_equation`, `valid_definition_old_language_iff`],
  [C7], [Specification from a typed witness], [`Specification.lean`:\ `SpecificationGate.`\ `valid_constant_from_typed_derivation`],
  [C8], [Subtype nonemptiness and Abs/Rep laws], [`TypeDefinitions.lean`: `TypeDefContract.nonempty`, `abs_rep`, `rep_in_range`, `rep_abs_of_pred`],
  [C9], [Finite old-language validity equivalence], [`Conservativity.lean`: `valid_interpretSequence_iff`],
  [C10], [Concrete non-derivability], [`Concrete.lean`: `falseSentence_not_derivable`],
  [C11], [Typed HOL core proof package], [`Soundness.lean`: `typed_hol_core_proof_complete`],
  [C12], [Type, evaluation and cross-model validity congruence], [`Types.lean`: `Ty.denote_congr`; `Congruence.lean`: `Term.eval_congr_κ`, `Term.eval_congr_vars`; `Transport.lean`: `valid_transport_κ`, `valid_iff_κ`],
  [C13], [Type-definition gate: admissible new model, three Abs/Rep laws, old-language invariance], [`TypeDefGate.lean`: `TypeDefGate.newTyCon_isAdmissible`, `valid_absRep`, `valid_repRange`, `valid_repAbs`, `valid_iff_old`; `ModelExtension.lean`: `TypeDefGate.laws`, `ModelExtension.valid_iff`],
)
}

No current Typed HOL theorem proves named-boundary conversion, MoonBit theorem
provenance, global-history registration, arbitrary new type-constructor
integration, dictionary resolution, or syntactic derivation erasure. These
remain explicit implementation or wider-theory obligations; their detailed
design and validation scenarios are retained in the preceding sections.
