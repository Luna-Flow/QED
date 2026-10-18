# Syntactic erasure of type definitions (research record, 2026-10-18)

- Status: research-only
- Audience: formalization contributors
- Authority: subordinate to [`qed_formal_spec.typ`](../../doc/attachments/qed_formal_spec.typ) and the Lean sources
- Scope: issue [#50](https://github.com/Luna-Flow/QED/issues/50); what is known, what fails, and the routes that remain
- Evidence boundary: pen-and-paper analysis against the Lean sources at `origin/main` after [#49](https://github.com/Luna-Flow/QED/pull/49); no Lean proof of the target statement exists
- Last reviewed: 2026-10-18 (updated after M1, [#54](https://github.com/Luna-Flow/QED/pull/54))

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

## Update after M1: what the logical-relation route needs

M1 is merged: with the connective rules, classical case analysis is available inside the
calculus, so a retraction `norm y := ε z. (P y ⟹ z = y) ∧ P z` with `⊢ P (norm y)` is now
derivable, and relativised equalities can be derived by `allIntro`/`impIntro`. A closer look at
the translation of free constants shows the restriction that M2 must impose.

* **Free constants cannot be translated.** Take a free constant `h : (α → bool) → α`. Its
  instance at `α := k` is forced by compatibility with `instType` to translate to `h` at the
  representation type, and that term is not self-related: `R(g, g')` only says `g` and `g'`
  agree on `P`, but `h` may distinguish them, so `R_k(h g, h g')` fails. The refl rule on
  `h_k` then has no translation. Replacing `h_k` by a default term breaks the compatibility
  with `instType`. The same happens for free type constructors `j` with `j(k)` arguments.
  Semantically this is harmless (the model assigns `h_k` an unrelated value), but a
  syntactic translation cannot represent it.
* **Defined constants and typedef-introduced constructors can be.** For a constant defined by
  a closed term, self-relatedness of the translation is the fundamental lemma applied to
  the right-hand side, by induction on the history. For an earlier typedef `J`, define
  `R_{J(τ)}(u, v) := R_{rep_J(τ)}(Rep u, Rep v)`; this is well behaved because the predicate
  of `J` is itself related to itself.
* So M2 is not a bookkeeping change. It restricts derivations to *scoped* ones: every constant
  occurring is introduced by a definition, a specification or a typedef of the history, and
  every type constructor other than `bool`, `ind`, `→` is introduced by a typedef of the
  history. That excludes the free constants and free type constructors that the total
  `Signature` currently allows, and the scope must be preserved by every rule (a scope
  predicate threaded through `HistoryDerivation`, or a derivation family indexed by an
  allowed-symbol set).

Revised estimate: M2 is a refactoring of the history calculus plus re-proving the definition and
specification erasures for scoped derivations; M3 and M4 are the relativisation proper
(relations at all types, the fundamental lemma for 25 rules, type-variable parameters,
the typedef laws). Several thousand lines of Lean; weeks to months. Whether the result is worth
it depends on whether the kernel's scoped histories are the intended object of the theorem,
which they are.

## Route A′: normalisation instead of a logical relation (current plan)

With classical reasoning available (M1), relativisation can be replaced by *normalisation*,
which keeps every equation an equation and needs no relativised quantifiers or relation
variables.

* **Retraction.** Let `norm y := ε z. (P y ⟹ z = y) ∧ P z` on the representation type. From a
  witness `⊢ ∃ z. P z` one derives (i) `⊢ P (norm y)`, (ii) `P y ⊢ norm y = y`, (iii)
  `⊢ norm (norm y) = norm y`. Extend to all types: `norm_k = norm`, `norm_{σ→τ} f = λx.
  norm_τ (f (norm_σ x))`, and `norm_τ = id` for `bool`, `ind`, type variables and other
  type constructors.
* **Translation `T`.** Send `k(args)` to the representation type with parameters `args`
  translated; `T` is homomorphic on the logical constructors; a variable `x : τ` goes to
  `norm_τ x`; `rep ↦ norm_{k→rep}(λx. x)`, `abs ↦ norm_{rep→k}(λx. x)`; equality, choice and
  every other constant `c_σ ↦ norm_τ(c_σ°)`. Every translated term is a fixed point of its
  `norm`, and `∀x. φ(norm x)` is exactly the relativised quantifier, so no hypotheses
  `P x` are needed and a sequent translates to a sequent with the same context.
* **Laws.** `T(Abs (Rep a)) = norm (norm (norm a))`, `T a = norm a`: law (1) is (iii); law (2)
  is (i); law (3) is (ii) applied twice. Each translated rule is the same rule on translated
  premises, with an idempotence rewrite for the rules that substitute (`beta`, `instTerm`,
  `allElim`, `exIntro`, `chooseWitness`), proved by induction on terms using the fixed point
  property. The witness is a hypothesis of the theorem (a typedef step is only created
  together with a derivable witness).
* **What remains hard.**
  1. *Type variables.* `norm_α = id` for a variable, but `instType` can replace `α` by a
     type containing `k`; `T(s[θ])` is then not derivably equal to `T(s)[θ°]`, because bound
     variables and `eq`/`choice` instances differ by a normalisation. Two ways out: push
     `instType` to the leaves first (an instType-free normal form of derivations, with
     instantiated typedef laws as leaves; needs substitution/instType commutation and
     composition of instantiations on arbitrary contexts), or give each type variable a
     normalisation parameter `ν_α` carried in the context.
  2. *Polymorphic constants.* A free polymorphic constant `c` (for example
     `h : (α → bool) → α`) has `T(c_k) = norm(c_rep)`, which is not the instance of
     `T(c_α)`; the translation is compatible with `instType` only for constants that are
     ground or defined (then unfold: translate the definition's right-hand side). So the
     theorem is for scoped histories whose other steps are first erased from the middle of
     the history (erasure of a definition or specification that is not at the head, which
     rewrites the gates of the steps above it).
  3. *Context management* for the translated sequents, the `norm` terms at every type and the
     commutation lemmas with `substitute`, `rename` and `instType` (the `Ren.mapTypes`-style
     machinery of `TermLaws.lean`, extended to substitutions and to a type translation that
     is not a type substitution).
* **Work list.** W1 instType-free normal form (or ν-parameters); W2 types, `norm_τ`,
  idempotence and fixed point lemmas; W3 term translation and its commutation with
  substitution up to derivable equality; W4 the 28 rule cases; W5 laws and the theorem for
  ground signatures; W6 middle erasure of definitions and specifications and the scoped
  statement for polymorphic constants. Roughly 5 000–8 000 lines of Lean. W1–W5 together give
  the theorem for signatures whose constants other than `rep`, `abs` have ground schemas; W6
  extends it to the kernel's scoped histories.

## Result for the parameter-free case

`TypeDefGate.typedef_conservative` (TdMain.lean) proves the statement for a type definition
without type parameters over the empty history, using Route A′ above. Two points differ from
the plan.

* The instantiation rule is handled by proving the translation at every type instance
  simultaneously (`hd_trans`), so neither an instantiation-free normal form nor relation
  variables were needed. Free polymorphic constants are not an obstacle in this formulation,
  because each constant instance is translated on its own.
* Two bookkeeping facts were needed: the translation of a constant uses a canonical instance
  substitution (the translated substitution on the type variables of the schema, the
  identity elsewhere), so that instances that agree on the schema translate alike, and the
  old-language sequent must carry canonical substitutions for the translation to be the
  identity on it.

Open: type parameters (the normalisation becomes a term polymorphic in the parameters), and
type definitions above older definitions, specifications or type definitions (the older steps
would be unfolded first, which needs erasure of a step that is not at the head of the history;
the example `c := λx. h (h x)` with a free polymorphic `h` shows that the older definitions
must be unfolded, not just kept).

## Where the proof stops, and why

Three extensions of `typedef_conservative` were examined.

1. **Instance junk (resolved by a syntax change).** A `Term.const c σ` carried a total `σ : TypeSub`, but only the values of
   `σ` on the type variables of `S c` matter. Two constants that differ only off that support
   are different Lean terms, and no rule identifies them. The translation therefore uses a
   canonical substitution (translated on the support, identity elsewhere), and the theorem needs
   the old-language sequent and the predicate to be canonical, so that the translation is the
   identity on them. This is harmless for terms that come from the kernel's lowering, but it is
   not stable under the operations the proof would use next: instantiating a canonical term by
   `θ` makes it non-canonical, and unfolding a definition `D` inside a predicate puts instances
   of the right-hand side (with off-support junk) into the predicate.
2. **Older steps.** A type definition above a definition or specification needs those steps
   unfolded first (the example `c := λx. h (h x)` with a free polymorphic `h` shows that keeping
   them as constants does not work). Unfolding is available for the head of a history (`erase_definition`,
   `erase_specification`) and would have to be extended to a step below a type definition. Its
   output predicate is non-canonical by point 1, and the gate of the type definition would no
   longer match the one used by the derivation. A type definition above another type definition
   additionally needs the normalisation at the older defined type, built from its `rep`/`abs`.
   The clean fix is a rule `⊢ const c σ = const c σ'` for `σ`, `σ'` agreeing on the schema's
   variables, available in `HistoryDerivation` (whose soundness already assumes a local base
   model); it is the identification the kernel makes implicitly. With it the canonicality
   hypotheses disappear, but every erasure theorem gets a new case and the translation needs a
   congruence lemma for the junk.
3. **Type parameters.** The development uses a closed representation type throughout:
   `Ty.tr` replaces `k(args)` by a fixed type, `norm` is a closed term, and the translation of
   `rep` and `abs` does not depend on the instance. With parameters, `tr (k(args))` is the
   representation type instantiated at the translated arguments, and `norm` becomes a term
   polymorphic in the parameters, instantiated at each use. The facts `nrm_range`, `nrm_fix`,
   `nrm_idem` would be derived once polymorphically and instantiated with the `instType` rule
   of the target, and the commutation lemmas would need the instantiated `norm`. This is a
   rework of every file of the development (about the size of the development itself), and it
   still leaves point 2, so it does not yet reach histories with older steps.

Resolution of point 1: a constant occurrence now stores its instance type with an `IsInst` proof, so
there is no junk and the canonicality hypotheses are gone (see the Unreleased changelog). Points 2
and 3 remain.

So the statement is now: proved for a parameter-free type definition over the empty history; open for parameters and for older steps, the latter blocked first by
the instance-junk identification above.

## After the syntax change: what the older-steps extension needs

The instance-junk problem is gone (a constant occurrence stores its instance type). The next
extension, a type definition above older steps, was analysed again against the sources.

* `core_trans` is already stated for an arbitrary target history, and the step lemmas are
  history-independent. Only `HistOk` (history is `[]` or `[G]`) and the `weaken` case of
  `hd_trans` fix the history.
* **Monomorphic older steps do not need unfolding.** If every constant declared below has a
  closed type (definitions, specifications, parameter-free typedefs), its theorems are ground
  and free of `k`, so `erase_trans_inst` makes the translation the identity on them and the
  step's own rule can be reused at the old history. The polymorphic case still needs unfolding:
  `c := λx. h (h x)` with a free polymorphic `h` gives `c[k] = λx. h[k] (h[k] x)`, whose
  translation wraps `h` in `norm` and is not an instance of the stored equation.
* **Even the monomorphic case needs a scoping hypothesis on the history.** A derivation at a
  suffix of the history must be lifted to the full history, and `weaken` requires the
  lifted sequent to avoid every newer step's constants. The translation introduces the
  predicate's constants, which may be newer than the suffix. The Lean signature is total, so
  nothing forbids a term below a step from mentioning that step's constant. The statement
  therefore needs a `Scoped` predicate on histories (data of a step avoids the symbols of newer
  steps and of `k`), and the translation target is always the full old history.
* The polymorphic case additionally needs erasure of a step that is not at the head of the
  history (rewrite the typedef's own predicate, check the gate fields `k_fresh`, `rep_fresh`,
  `abs_fresh` still hold, which also needs scoping).

Estimated size: the monomorphic variant is a rework of `HistOk`/`ext_trans`/`hd_trans` plus a
history-scoping predicate; the polymorphic variant is a second development of the size of
`Unfold.lean` + `SpecErasure.lean`. Neither is started.

## Update: older definitions and specifications are covered

The polymorphic case was done by unfolding, not by monomorphising. `TypeDefGate.unfold` rewrites
the predicate of the type definition with a declaration below it unfolded; the gate fields
(`closed`, `k_fresh`, `rep_fresh`, `abs_fresh`) are preserved under `Unfolder.Below`, which
only asks that the declaration's own data does not mention `k`, `rep`, `abs`. The three laws of
the old gate unfold to the three laws of the new gate (`unfold_law`), so the `typedef` rule is
reproduced at the shorter history and a derivation at `G :: U :: es` becomes one at `G[U] :: es`
(`HistoryDerivation.erase_below`). Iterating over the list of declarations ends at the base
theorem on the empty history. No scoping predicate on histories was needed in the end: the
`weaken` case of the type definition is handled by erasing the head declaration from the
inner derivation and weakening by the new gate, and the old-language condition of the new
gate follows from the bounds. Remaining: type parameters, and type definitions below.

## Update: older parameter-free type definitions

Unlike definitions and specifications, an older type definition cannot be unfolded, but it does
not need to be when it has no parameters: its constants have closed types and its laws are
ground. If the new type definition's symbols do not occur in those laws, the translation is the
identity on every rule instance of the older step. The translation theorem was therefore
generalised from the target history `[]` to the old history `T` (all older steps), and the
`weaken` case no longer needs the translated sequent to be in the old language of the step: the
rule instances of the older steps are lifted from their own suffix of `T` to `T`, using that
the newer type definitions between them do not occur in their laws (`Older`). The scoping is a
hypothesis because the Lean signature is total and nothing else forbids it. Remaining:
type parameters, and older type definitions with parameters.

## Update: phantom parameters, and why genuine parameters are harder than expected

The proof used `n = 0` only to obtain two facts: the representation type is closed and the
predicate is ground. `n` itself never restricted `tr_con_pos`, the types of `rep` and `abs`, or
the laws. The standing hypothesis `Ok` is now exactly those two facts, so type parameters that
occur only in the new type (newtype-style wrappers) are covered.

For a representation type or predicate that mentions the parameters, the earlier estimate
("make `norm` polymorphic in the parameters") is too low. `norm` at an instance `k(args)` must
be built from the translation of the predicate at that instance, not from the raw instance of
the predicate: when `args` contains `k`, the translated predicate has `norm` wrappers around the
constants at those types, and the raw instance is not equivalent to it. The translation of the
predicate at an instance is itself a translation at a smaller nesting depth of `k`, so the
translation is recursive in that depth (well-founded recursion, or a fuel parameter with a
monotonicity lemma), and the laws at depth `d` need the translation of the witness derivation at
depth `d - 1`, so the main induction becomes an induction on the depth as well. This touches the
definition of `trans` and every lemma about it, not only the norm. It is a separate development.

## Parametric type definitions: why a rewrite of the `Td*` files is not enough

The previous section says the translation becomes recursive in the nesting depth of `k`. Working
the design through shows that this is not the only obstruction.

1. **Oracle form.** The recursion can be removed from `trans` by abstracting the normaliser at
   each type with head `k` into an oracle `N`. `trans N` is then structurally recursive, and the
   step lemmas only need `N` to be *good*: `⊢ Q(N u)`, `Q u ⊢ N u = u`, with `Q` the translation
   of the predicate at that instance. `N` itself is defined by well-founded recursion on the
   depth of `k`, and `Good N` is proved by strong induction on the depth.
2. **The witness at a nested instance.** `Good N` at `k(args)` needs `⊢ ∃z. Q z`, the
   translation of the witness derivation `hwit` at the instance `θ_τ` of the parameters. That is
   an application of the main translation theorem to `hwit`, with an oracle that is good only for
   depths below `τ`. The proof of the main theorem is an induction over the derivation, and it
   needs `Good N` at every type the derivation visits. For `hwit` those types stay below the
   depth of `τ` only if every sequent and every instantiation inside `hwit` is free of `k`.
3. **A derivation is a proof.** `HistoryDerivation` is a `Prop`. A statement about the types
   that occur inside a derivation cannot be defined by recursion on it (any two proofs are
   definitionally equal). So "`hwit` is `k`-free internally" and "the translation of `hwit` at
   `θ` needs fuel `B`" have no definition. The usual remedy is a second, depth-indexed copy of
   the calculus. `hwit` is then transformed by `erase_definition`, `erase_specification` and
   `erase_chain` along the way (`TdAll`), so each of those would need a version for the copy
   as well.

Without internal `k`-freeness the induction does not close: the fuel needed to translate `hwit`
at an instance of depth `d` can be `d` or more, and the oracle at that depth is the one being
constructed. The expected size is therefore a second derivation calculus and a second set of
erasure theorems, on top of the rewrite of `Td*`, not a rewrite alone. The alternative is route A
(a logical relation), where the relation at `k(args)` is structurally recursive in the type and
no fuel appears, but it needs the fundamental lemma of the whole calculus.

Parametric type definitions whose representation type or predicate mentions the parameters thus
stay open. They are not needed for kernel soundness, which uses the semantic conservativity
theorem.

## Update: parametric type definitions are done

The analysis in the previous section assumed that the translated witness at a nested instance
needs control of the types the witness derivation visits. It does not, once the oracle is
staged. The translation theorem for a derivation that does not use the laws of the new type
definition (`hd_trans_chain` at a suffix of the old history) requires only that the oracle is
idempotent. The oracle at stage `d` is the identity at every type of depth above `d` (which is
idempotent) and the retraction of the translated predicate at the types of depth `d`. The witness
at an instance of depth `d` is the translation of the old witness instantiated at the arguments,
computed with stage `d - 1`; whatever deeper types its derivation visits are translated by the
identity oracle, which is harmless. So no second calculus and no `k`-free copy of the witness is
needed, and the `HDF` calculus and the constructor-substitution map considered earlier were
discarded unused.

Two corrections to the plan were needed along the way. The normaliser at `k(a)` must also project
onto the elements fixed by the normalisation at the representation type `R[a]`, which is
nontrivial when `a` mentions `k` (`Qc`); without it the first law fails. And everything that
depends on the instance had to be made to depend only on its first `n` arguments (`args`), so
that laws for instances with the same arguments transport trivially.
