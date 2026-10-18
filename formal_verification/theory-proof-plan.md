# Typed HOL proof plan

- Status: active formal work plan
- Audience: formalization contributors and reviewers
- Authority: [`qed_formal_spec.typ`](../doc/attachments/qed_formal_spec.typ)
- Scope: Lean definitions, theorem dependencies and explicit mathematical limits
- Boundary: this plan does not define MoonBit behavior or certify source-level refinement
- Last reviewed: 2026-10-14

The short [branch contract](branch_contract.md) defines promotion order. This
file is its technical appendix: it names the Lean modules and the theorem
families that must exist before a branch can be promoted. Cross-dimensional
status belongs to the machine-readable
[`qed_obligations.json`](../doc/manual/qed_obligations.json), not to another
hand-maintained matrix here.

## Dependency graph

1. `Types.lean` defines `Ty`, substitutions, denotations, admissible carriers and non-empty interpretations.
2. `Terms.lean` defines intrinsically typed De Bruijn terms, renaming, capture-avoiding substitution and type instantiation.
3. `Evaluation.lean` proves renaming, substitution and beta evaluation laws.
4. `Instantiation.lean` proves type-instantiation and choice coherence.
5. `Rules.lean` proves preservation for the primitive rules, weakening and witness-based choice.
6. `Derivation.lean` packages the twenty-five constructors (thirteen equational and choice rules including the exact infinity sentence, and twelve connective and quantifier rules from `ConnectiveRules.lean`); `derivation_sound` is the induction theorem.
7. `Definitions.lean`, `Specification.lean` and `TypeDefinitions.lean` prove the local extension laws.
8. `ModelExtension.lean` and `ExtensionDerivation.lean` interpret newest-first histories of definition, specification and type-definition steps. Witnesses are derivations at the preceding history; typedef laws are selected by `TypeDefLaw`; old derivations lift only when their sequents omit the new identifiers.
9. `HistoryDerivation.lean` embeds those extension products and closes them under the core rules at one fixed total signature. The examples and negative audits check non-vacuity, empty predicates and repeated identifiers.
10. `Conservativity.lean`, `Congruence.lean` and `Transport.lean` prove fixed-signature old-language validity transport. `Concrete.lean` supplies non-triviality and non-derivability examples.
11. `TypeDefGeneric.lean`, `TypeDefGate.lean`, `TypeDefLocal.lean` and `TypeDefDerivationExamples.lean` give the predicate-subtype model, Rep/Abs laws, locality and a concrete one-element subtype.
12. `Soundness.lean` exports `QEDFV.HOL.typed_hol_core_proof_complete`; it is a package theorem, not a completeness theorem or a growing-theory result.

The current induction proves validity at the history's model pair. History
freshness is carried as a well-formedness premise; semantic induction uses the
local gate conditions and locality of the base model. This distinction is
intentional and must remain visible in later refinements.

## Kernel-to-Lean correspondence targets

| Implementation surface | Lean target | Current boundary |
| --- | --- | --- |
| `refl_checked`, `assume_checked`, `add_assum_checked` | `Derivation.refl`, `.assume`, `.addAssum` | Core semantics proved |
| `trans_checked`, `mk_comb_rule_checked`, `abs_rule_checked`, `beta_rule_checked` | corresponding derivation constructors | Core semantics proved |
| `eq_mp_checked`, `deduct_antisym_rule_checked` | `.eqMp`, `.deduct` | Core semantics proved |
| Type and term instantiation | `.instType`, `.instTerm` | Typed substitution preservation proved |
| `ks_define_const` and `ks_define_const_thm` | `DefinitionGate`, `ExtensionDerivation.definition` | Fixed signature and local semantic law; name audit is separate |
| `ks_specify_const` | `SpecificationExtension`, `ExtensionDerivation.specification` | Fixed signature and witness semantics; executable certificate correspondence is open |
| `ks_register_type_definition` | `TypeDefGate`, `ModelExtension.typeDefinition`, `HistoryDerivation.typedef` | Fixed-signature model-pair semantics; allocation and erasure are open |
| `ks_ind_infinity_axiom` | `Derivation.indInfinity`, `indInfinitySentence` | Exact Lean sentence proved; the MoonBit registration is an audit marker, not connected to it |

The frontend currently represents logical connectives through defined constants,
while the Lean term grammar has primitive connective constructors. A future
refinement must prove the translation, evaluation, substitution and instantiation
compatibility for each definition. Seeing the right name or an `ind` occurrence
does not establish that correspondence.

## Mathematical limits

The current development uses a total `Signature := Nat → Ty` and explicit
constructor interpretations. It proves fixed-signature semantic validity and
old-language transport. It does not yet prove:

- a growing signature with embeddings, allocation and model transport;
- preservation of every committed declaration equation across growth;
- MoonBit representation, state or theorem-constructor refinement;
- parser, elaborator, tactic, replay or mutable-scope correctness;
- syntactic type-definition erasure, which would require a relativisation translation;
- an independent checker for exported derivation certificates.

These limits are evidence boundaries, not reasons to weaken the normative
specification. The relevant open entries are `HOL-GROW-001`,
`HOL-INFINITY-001`, `KERNEL-BOUNDARY-001`, `KERNEL-PROVENANCE-001`,
`FRONTEND-LOWERING-001` and `REFINEMENT-001` in the registry.

## Planned growing-signature obligations

The next branch must establish the following in order:

| ID | Required result | Acceptance evidence |
| --- | --- | --- |
| `GROW-SIG-001` | A declaration state records allocated constant schemas and constructor arities, rejects duplicate or forward references, and preserves old entries | Extend `DeclarationAllocation.lean` with constructor allocation and state well-formedness |
| `GROW-SIG-002` | Signature embeddings transport types, contexts and intrinsically typed terms and commute with substitution and instantiation | Embedding identity/composition and typing lemmas |
| `GROW-SIG-003` | Evaluation and sequent validity transport along an embedding | Term evaluation transport followed by sequent validity transport |
| `GROW-SIG-004` | Every extension step preserves old commitments and has a model extension compatible with the embedding | Definition, specification and typedef cases with explicit committed-equation preservation |
| `GROW-SIG-005` | A growing-history derivation composes the transported core and extension rules | History induction over the growing state, followed by a soundness theorem |

No proposed obligation becomes a published result until its Lean declarations,
axiom audit and registry evidence are present.

## Verification

Run the formal gate from the repository root:

```text
python3 tools/qed_formal_gate.py
```

The gate builds the Lean project, runs the axiom audit and checks the registry
and generated view. The checked-in `formal_verification/axioms.txt` records the
current foundations: `propext`, `Classical.choice` and `Quot.sound`.
