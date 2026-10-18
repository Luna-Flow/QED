# Syntactic erasure of type definitions (research record, 2026-10-18)

- Status: research-only
- Audience: formalization contributors
- Authority: subordinate to [`qed_formal_spec.typ`](../../doc/attachments/qed_formal_spec.typ) and the Lean sources
- Scope: issue [#50](https://github.com/Luna-Flow/QED/issues/50); what is known, what fails, and the routes that remain
- Evidence boundary: pen-and-paper analysis against the Lean sources at `origin/main` after [#49](https://github.com/Luna-Flow/QED/pull/49); no Lean proof of the target statement exists
- Last reviewed: 2026-10-18

## The statement

The target is expressible with existing definitions:

```lean
theorem HistoryDerivation.typedef_conservative (G : TypeDefGate S)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (.typeDefinition G :: es) s)
    (hOld : (ModelExtension.typeDefinition G).oldLanguage s) :
    HistoryDerivation S es s
```

Its semantic counterpart is proved (`typed_global_semantic_conservativity_models`). Syntactic
conservativity does not follow from it, because `Derivation` is not known to be complete for
the standard semantics. The analogous statements for definitions and specifications are
proved (`definition_conservative`, `specification_conservative`) by replacing the new constant
with a closed term.

## Why the constant-replacement method does not extend

A type definition adds a type, not a constant. The three laws are
(1) `⊢ Abs (Rep a) = a`, (2) `⊢ P (Rep a)`, (3) `P r ⊢ Rep (Abs r) = r`.
Any translation that sends the new type `k(..)` to a type of the old language needs laws
(1)–(3) to translate to derivable sequents.

* Sending `k` to `repTy` with `Rep`, `Abs` the identity makes (1) and (3) trivial but (2)
  becomes `⊢ P a` for a free `a`, which is not derivable. Such a map would inject `repTy`
  into the subtype `P`, which is false in general.
* A retraction `norm : repTy → repTy` with `⊢ P (norm y)` repairs (2), but deriving it needs a
  `y`-dependent element of `P`; the witness premise only gives a closed one, and a
  case split on `P y` needs rules for `imp`, `conj`, `ex`.
* Carrying hypotheses `P x` for variables of type `k` fails at `instTerm` with a term such as
  `Abs r`, and has no analogue for variables of type `k → k` or `j(k)`.
* The type must have exactly the elements of `P`; HOL without subtypes cannot name such a
  type, so the usual proof relativises quantifiers and equalities instead.

## The Lean calculus versus the kernel

`Derivation` has only equational rules, `chooseWitness` and `indInfinity`. The connectives
and quantifiers (`truth`, `falsity`, `conj`, `imp`, `all`, `ex`) are primitive term
constructors with a semantics and no rules. The kernel has no such constructors: its terms are
`Var`, `Const`, `Comb`, `Abs`, and the connectives are constants defined in the propositional
prelude, with their rules derived as theorems. The specification already records this as a
refinement contract. For relativisation this means the Lean calculus cannot derive
`∀x. P x ⟹ f x = g x` from `P x ⊢ f x = g x`.

## Route A: relativisation by a logical relation

Translate each type `τ` to `τ°` (replace `k(args)` by `repTy[args°]`) together with a
partial equivalence relation `R_τ`: `R_k(x, y) := P x ∧ x = y`,
`R_{σ→τ}(f, g) := ∀x y. R_σ(x, y) ⟹ R_τ(f x, g y)`, equality on `bool` and `ind`.
A term `t : τ` translates to `t°` with `R_τ(t°, t°)` derivable, and a derivation of a
sequent translates to one of the relativised sequent; a fundamental lemma is proved rule by
rule. Requirements:

1. Rules for the connectives and quantifiers, plus classical reasoning, in `Derivation`
   (mirroring the kernel's derived theorems). Soundness of each is immediate; the cost is the
   new cases in every induction, including the definition and specification erasure
   (one `replConst_step_*` lemma per rule).
2. Type variables need predicate parameters (Reynolds-style), because `instType` substitutes
   a type containing `k` for a variable; the translation must commute with it.
3. A treatment of every other type constructor `j` applied to a type containing `k`, and of
   every constant whose instances mention `k`. For a type constructor with no definition the
   relation `R_{j(τ)}` cannot be defined. The total `Signature` and `Ty.con` allow arbitrary
   such `j`, so a restriction is needed: every constructor other than `k` comes from an earlier
   typedef (then `R_{j(τ)}` is `R` on the representation type, by induction on the history),
   and every constant comes from a definition or specification (these are erased first, since
   they are newer or are unfolded into their definition).
4. Classical case analysis and a retraction `norm` derived inside the calculus.

Estimate: this is a development of several thousand lines of Lean (relations, fundamental
lemma, a derived classical logic) over a restricted signature, i.e. months, with the
restriction itself a new modelling decision.

## Route B: completeness and model expansion

If `Derivation` were complete for a class `𝓜` of models closed under the typedef model
expansion, conservativity would follow: an old-language sequent derivable after the
definition is valid in every `𝓜`-model of the extension, every `𝓜`-model of the old theory
expands to one (the existing construction), hence it is valid in every `𝓜`-model of the old
theory and derivable by completeness. This needs a Henkin-style completeness theorem for the
weak calculus and a class `𝓜` containing the expanded models; the existing models are full
(standard) models, for which the calculus is expected to be incomplete. Not attempted.

## Route C: do not prove it

Kernel soundness needs only the semantic result, which is proved. The syntactic result is
a proof-theoretic strengthening. Definitions and specifications, the cases the kernel
exercises most, are already covered.

## Recommendation

1. Keep the statement as an explicit open target (above); do not add it to the Lean library
   with `sorry`, which the gate rejects.
2. If the work is wanted, do Route A in stages, each independently useful:
   * M1: connective and quantifier rules in `Derivation`/`HistoryDerivation`, with soundness and
     the extra erasure step lemmas. This also narrows the gap to the kernel's prelude.
   * M2: define the restricted signature class (all type constructors from typedefs, all
     constants from definitions or specifications) and show the erasures preserve it.
   * M3: the logical relation for the base types and arrows, and the fundamental lemma for the
     core rules.
   * M4: type-variable parameters and the typedef laws; the theorem.
   Decision point after M2: if the restricted class excludes derivations the kernel needs, stop.
3. Otherwise close #50 as documented.
