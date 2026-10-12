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
11. `HOL/Soundness.lean` exports `typed_hol_core_proof_complete`, a package for
    the checked core and its semantic results. It is not a completeness theorem
    or a full growing-theory development.

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
| `ks_register_type_definition` | `TypeDefContract` | Nonempty predicate subtype and Abs/Rep laws | No user type-constructor node in `Ty`; interpretation update is not modeled |
| `ks_ind_infinity_axiom` | `Derivation.indInfinity`; `indInfinitySentence` | Exact infinity sentence is valid in every model, witnessed by `Nat.succ` | MoonBit registration gate is not verified; see issue #7 |
| eta | no kernel primitive found | Not applicable | Not a primitive of the current kernel calculus |

## Acceptance Matrix

| Obligation | Lean evidence | Status |
| --- | --- | --- |
| Typed core syntax and non-empty carriers | `HOL/Types.lean`, `HOL/Terms.lean` | proved |
| Renaming, substitution, beta | `HOL/Evaluation.lean` | proved |
| Type instantiation and selector coherence | `HOL/Instantiation.lean` | proved |
| Twelve core rule preservation cases and object-language infinity admission | `HOL/Rules.lean`, `HOL/Derivation.lean`, `HOL/Infinity.lean` | proved |
| Arbitrary-signature non-triviality | `signatureGenericFalseSentence_not_derivable` | proved |
| Definition equation under its model override | `valid_definition_equation` | proved semantically |
| Specification from a closed typed witness | `valid_choose_from_witness`, `SpecificationGate.valid_constant_from_typed_derivation` | proved semantically |
| Type-variable closure under instantiation | `DefinitionGate.instType_type_vars_closed`, `SpecificationGate.instType_type_vars_closed` | proved |
| Predicate-subtype type-definition laws | `HOL/TypeDefinitions.lean` | proved at carrier level |
| Finite old-language validity equivalence | `valid_interpretSequence_iff` | proved for fixed-signature overrides |
| Object-language infinity admission | `Derivation.indInfinity`, `indInfinitySentence_valid` | proved for the exact sentence in all models |
| History-indexed definition/specification derivations | `extension_derivation_sound` | proved for fresh constant IDs over a fixed signature |
| Growing-signature syntax and semantic interpretation | no history-indexed `Signature` or type constructors | open |
| User type-constructor syntax and semantics | no constructor in `Ty` | open |
| MoonBit-to-Lean refinement and theorem provenance | no Typed HOL theorem | excluded; issue #15 remains open |
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

The extension interpretation is still over a fixed `Signature`; its
`typeDefinition` case is the identity. User type constructors must become part
of both syntax and carrier interpretation before typedef soundness can be
claimed at the object-language level. This limitation is explicit in the
current theorem statements.
