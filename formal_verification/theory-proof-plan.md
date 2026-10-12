# Typed HOL Proof Plan

- Status: Typed HOL is the sole formal proof line.
- Authority: [QED Typed HOL Core](../doc/attachments/qed_formal_spec.typ).
- Scope: intrinsically typed core derivations, history-indexed constant
  extension derivations, their semantic soundness, and non-triviality witnesses.
- Excluded: MoonBit refinement, parser/tactic correctness, mutable signature
  provenance, and derivation erasure for a growing theory.

## Proof Dependency

1. `HOL/Types.lean` defines the four core types, substitutions, denotations,
   admissibility, and non-empty carriers.
2. `HOL/Terms.lean` defines intrinsically typed De Bruijn terms, renaming,
   capture-avoiding substitution, and type instantiation.
3. `HOL/Evaluation.lean` defines environments and interpretations and proves
   renaming, substitution, and beta evaluation laws.
4. `HOL/Instantiation.lean` proves choice coherence and semantic type
   instantiation.
5. `HOL/Rules.lean` proves direct preservation for the core rules, including
   `valid_add_assum` and witness-based `valid_choose_from_witness`.
6. `HOL/Derivation.lean` has thirteen constructors, including object-language
   infinity admission. `derivation_sound` proves
   soundness by induction, with a case for every constructor.
7. `HOL/Definitions.lean`, `HOL/Specification.lean`, and
   `HOL/TypeDefinitions.lean` prove local semantic extension contracts.
8. `HOL/ExtensionDerivation.lean` defines `ExtensionDerivation S es`, indexed
   by newest-first constant-extension histories. Specification steps require a
   witness derivation at the preceding history; definition and specification
   steps carry history-ID freshness side conditions, and old derivations lift
   only across extensions absent from their sequents. The soundness induction
   does not use those history-freshness premises: they constrain well-formed
   histories, while local gate freshness is used by the product validity lemmas.
   This theorem does not establish global consistency of all prior equations.
9. `HOL/Conservativity.lean` composes finite, old-language validity equivalence
   for pointwise constant overrides on one fixed signature.
10. `HOL/Concrete.lean` proves concrete and signature-generic non-derivability.
11. `HOL/Congruence.lean` proves that evaluation depends only on the type
    variables (`Term.annotVars`), type-constructor ids (`Term.tyCons`) and
    constants occurring in a term (`Term.eval_congr`, `Term.eval_congr_κ`,
    `Term.eval_congr_vars`); `HOL/Transport.lean` lifts this to validity across
    constructor interpretations (`valid_transport_κ`, `valid_iff_κ`) and derives
    the old-language statements as corollaries; `HOL/TyConCongruence.lean` has the
    worked example and the counterexample showing that the sequent's constructor
    ids cannot be dropped from the hypothesis.
12. `HOL/TypeDefGeneric.lean` defines the subtype carrier `SubCarrier` (predicate
    subtype with a witness, `PUnit` without) and its rep/abs laws;
    `HOL/TypeDefGate.lean` defines `TypeDefGate`, the new constructor interpretation
    `TypeDefGate.newTyCon` and constant interpretation `TypeDefGate.newConst`, proves
    the new constructor interpretation admissible, the three Abs/Rep laws as valid
    sequents about `Rep`/`Abs` terms (`valid_absRep`, `valid_repRange`, `valid_repAbs`;
    only `valid_repRange` needs the witness hypothesis `WitnessAt`) and old-language
    invariance of the step (`valid_iff_old`); `HOL/ModelExtension.lean` adds model pairs
    `Model` and `ModelExtension` as a parallel version of `Extension`;
    `HOL/TypeDefExamples.lean` has a nonempty and an empty predicate.
13. `HOL/Soundness.lean` exports `typed_hol_core_proof_complete`, a package for
    the checked core and its semantic results. It is not a completeness theorem
    or a full growing-theory development.

## Connective and Infinity Refinement Contract

The Lean `Term` grammar gives truth, falsity, conjunction, implication, universal
quantification, and existential quantification primitive constructors. The
kernel frontend currently represents these forms through defined constants, so
the eventual MoonBit-to-Lean refinement must map each definition to its Typed HOL
constructor and prove the defining equation through lowering, evaluation,
substitution, and type instantiation. The infinity registration must lower to
the exact `indInfinitySentence`; a type match or an occurrence of `ind` alone is
not evidence of that correspondence.

The validity theorem for this sentence uses the fixed interpretation
`Ty.ind.denote κ ρ = Nat` and the witness `Nat.succ`. It is therefore a theorem
about the present fixed type grammar, not about every possible carrier for an
abstract type named `ind`.

## Kernel-to-Lean Map

| Kernel primitive or extension | Lean representation | What is proved | Boundary |
| --- | --- | --- | --- |
| `refl_checked` | `Derivation.refl`; `valid_refl` | Equality reflexivity | Checked |
| `assume_checked` | `Derivation.assume`; `valid_assume` | Singleton-hypothesis validity | Checked |
| `add_assum_checked` (#10) | `Derivation.addAssum`; `valid_add_assum` | Weakening by an added boolean assumption | Checked in core calculus |
| `trans_checked` | `Derivation.trans`; `valid_trans` | Equality transitivity | Checked |
| `mk_comb_rule_checked` | `Derivation.mkComb`; `valid_mkComb` | Function and argument congruence | Checked |
| `abs_rule_checked` | `Derivation.abs`; `valid_abs` | Extensionality under a binder | Checked |
| `beta_rule_checked` | `Derivation.beta`; `valid_beta` | Beta equation | Checked |
| `eq_mp_checked` | `Derivation.eqMp`; `valid_eqMp` | Boolean equality elimination | Checked |
| `deduct_antisym_rule_checked` | `Derivation.deduct`; `valid_deduct` | Deduction antisymmetry | Checked |
| type and term instantiation | `Derivation.instType`, `.instTerm`; `valid_inst_type`, `valid_inst_term` | Typed substitution preservation | Checked |
| `ks_define_const`, `ks_define_const_thm` | `DefinitionGate`, `ExtensionDerivation.definition`; `extension_derivation_sound` | Defining equation; local RHS freshness is used, history-ID freshness is carried but unused by soundness | Fixed signature; name audit remains an implementation boundary |
| `ks_specify_const` | `SpecificationExtension`, `ExtensionDerivation.specification`; `extension_derivation_sound` | Named constant theorem from a witness derivation in the preceding history; local gate freshness is used, history-ID freshness is carried but unused by soundness | Fixed signature; MoonBit certificate remains an implementation boundary |
| `ks_register_type_definition` | `TypeDefGate`, `TypeDefGate.interpret`, `ModelExtension.typeDefinition`; carrier-level `TypeDefContract` | New constructor interpretation (predicate subtype or `PUnit`) is admissible; `Abs (Rep a) = a`, `P (Rep a)` (under the witness hypothesis `WitnessAt`) and `P r ⊢ Rep (Abs r) = r` are valid in the new model; sequents not mentioning `k`, `rep`, `abs` keep their validity (for a local old interpretation) | Semantics over model pairs only: no `ExtensionDerivation` constructor, so the laws are not yet derivable in a history; history freshness of `k`, `rep`, `abs` and the kernel's string-name lowering are not modelled; MoonBit gate not verified |
| `ks_ind_infinity_axiom` | `Derivation.indInfinity`; `indInfinitySentence` | Exact infinity sentence is valid in every model, witnessed by `Nat.succ` | MoonBit registration gate is not verified; see issue #7 |
| eta | no kernel primitive found | Not applicable | Not a primitive of the current kernel calculus |

## Acceptance Matrix

| Obligation | Lean evidence | Status |
| --- | --- | --- |
| Typed core syntax and non-empty carriers | `HOL/Types.lean`, `HOL/Terms.lean` | proved |
| Renaming, substitution, beta | `HOL/Evaluation.lean` | proved |
| Type instantiation and selector coherence | `HOL/Instantiation.lean` | proved |
| Thirteen derivation-constructor preservation cases, including object-language infinity admission | `HOL/Rules.lean`, `HOL/Derivation.lean`, `HOL/Infinity.lean` | proved |
| Arbitrary-signature non-triviality | `signatureGenericFalseSentence_not_derivable` | proved |
| Definition equation under its model override | `valid_definition_equation` | proved semantically |
| Specification from a closed typed witness | `valid_choose_from_witness`, `SpecificationGate.valid_constant_from_typed_derivation` | proved semantically |
| Type-variable closure under instantiation | `DefinitionGate.instType_type_vars_closed`, `SpecificationGate.instType_type_vars_closed` | proved |
| Type, evaluation and cross-model validity congruence over constructor ids and type variables | `Ty.denote_congr`, `Term.eval_congr_κ`, `Term.eval_congr_vars`, `valid_transport_κ`, `valid_iff_κ`, `valid_allEq_one_unchanged`, `valid_allEq_zero_changes` | proved; used by the type-definition gate |
| Predicate-subtype type-definition laws | `HOL/TypeDefinitions.lean` | proved at carrier level |
| Type-definition gate: admissible new model | `TypeDefGate.newTyCon_isAdmissible` | proved |
| Type-definition Abs/Rep laws as valid sequents about `Rep`/`Abs` terms | `TypeDefGate.valid_absRep`, `valid_repAbs` (no witness needed), `valid_repRange` (under `WitnessAt`), `TypeDefGate.laws`, `TypeDefGate.laws_of_witness_valid` | proved semantically; the witness hypothesis is necessary (`falseGate_repRange_not_valid`) and is discharged in the derivation step from `⊢ P w` |
| Old-language invariance of a type-definition step | `TypeDefGate.valid_iff_old`, `valid_iff_old_canonical`, `ModelExtension.valid_iff` | proved for a local old interpretation (the canonical one is local); not yet composed over histories |
| Finite old-language validity equivalence | `valid_interpretSequence_iff` | proved for fixed-signature overrides |
| Object-language infinity admission | `Derivation.indInfinity`, `indInfinitySentence_valid` | proved for the exact sentence in all models |
| History-indexed definition/specification derivations | `extension_derivation_sound` | proved for fresh constant IDs over a fixed signature |
| Growing-signature syntax and semantic interpretation | no history-indexed `Signature` or type constructors | open |
| User type-constructor syntax and semantics | `Ty.con` node and `TyConVal` interpretation, core calculus sound for every admissible `κ`; validity is invariant under changing `κ` on constructor ids a sequent does not mention; type-definition gate semantics over model pairs; no derivation constructor, history freshness or history-indexed `κ` | partial |
| MoonBit-to-Lean refinement and theorem provenance | no Typed HOL theorem | refinement excluded; MoonBit lineage invariant is tested separately |
| Syntactic conservativity/derivation erasure | no growing-theory derivation | open |

The levels of extension evidence must remain distinct: local semantic laws,
history-indexed derivations over a fixed signature, growing-signature
derivations, and syntactic erasure are different results. This development
proves the first two where listed; it does not identify them with the latter two.

## Open Kernel/Specification Issues

- [Issue #7](https://github.com/Luna-Flow/QED/issues/7): the MoonBit infinity
  anchor gate accepts a theorem that merely mentions `ind`; Lean proves the
  exact object-language sentence but does not certify that executable gate.
- [Issue #8](https://github.com/Luna-Flow/QED/issues/8): the specification gate
  witness certificate differs from the mathematical witness contract. The Lean
  `SpecificationGate` is a semantic object, not a proof of MoonBit certificate
  validation.
- [Issue #9](https://github.com/Luna-Flow/QED/issues/9): definition
  non-circularity is checked by constant name. Lean uses `DefinitionGate.fresh`
  to prove the local defining equation, but the separate history-ID freshness
  premise in `ExtensionDerivation.definition` is unused by soundness and does
  not prove the global dependency audit.
- [Issue #10](https://github.com/Luna-Flow/QED/issues/10): `add_assum_checked`
  was absent from the mapping. It now maps to `Derivation.addAssum` and has a
  direct semantic preservation proof.
- [Issue #13](https://github.com/Luna-Flow/QED/issues/13): PR CI should validate
  MoonBit and Lean. This work adds the cached Lean job; MoonBit refinement is
  still a separate soundness obligation.

## Trust Basis

`formal_verification/axioms.txt` records the `#print axioms` output for the
public core proof and representative metatheorems. No project-defined axiom is
used to assert soundness. The Lean/mathlib foundations reported by the audit are
`propext`, `Classical.choice`, and `Quot.sound`.

## Verification

- `lake build`: all targets in `formal_verification` build.
- Axioms are captured by the checked-in `HOL/AxiomAudit.lean` declarations and
  recorded in `axioms.txt`.
- Manuscript anchors are compiled against the named Lean modules.
- `typst compile` and `lunadoc check . --compile` validate the normative
  specification and its references.

The extension interpretation is still over a fixed `Signature`. The legacy
`Extension.typeDefinition` case is the identity; the type-definition step is
modelled separately over model pairs (`ModelExtension`) and is not yet a
constructor of `ExtensionDerivation`, so typedef soundness at the level of
derivations in a history cannot be claimed. Old-language invariance across a
change of the constructor interpretation needs locality of the old constant
interpretation, which the canonical interpretation has and which definition
steps preserve only under an annotation-closure condition the present
`DefinitionGate` does not state. These limitations are explicit in the current
theorem statements.
