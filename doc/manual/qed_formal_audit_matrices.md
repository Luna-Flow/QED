# Typed HOL audit matrix

Audit basis: `doc/attachments/qed_formal_spec.typ` and
`formal_verification/QEDFV/HOL`. Status means the stated Lean proposition
typechecks; it does not silently certify the separate MoonBit implementation.

## Proof-obligation matrix

| Obligation | Lean evidence | Status |
| --- | --- | --- |
| Typed syntax and non-empty carriers | `HOL/Types.lean`, `HOL/Terms.lean` | proved |
| Renaming, substitution, beta | `HOL/Evaluation.lean` | proved |
| Type instantiation and choice coherence | `HOL/Instantiation.lean` | proved |
| Primitive rule preservation | `HOL/Rules.lean` | proved |
| Inductive derivation soundness | `HOL/Derivation.lean` | proved |
| Definition semantic equation and old-language invariance | `HOL/Definitions.lean` | proved |
| Specification validity and old-language invariance | `HOL/Specification.lean` | proved |
| Predicate-subtype type-definition laws | `HOL/TypeDefinitions.lean` | proved |
| Type-definition gate semantics (new model, Abs/Rep laws, old-language invariance) | `HOL/TypeDefGate.lean`, `HOL/ModelExtension.lean` | proved over model pairs |
| Locality preserved by definition, specification and type-definition steps | `HOL/Definitions.lean`, `HOL/Specification.lean`, `HOL/TypeDefLocal.lean` | proved (gate closure fields stated for `Term.annotVars`) |
| Type-definition derivation constructor; soundness and old-language conservativity along a history | `HOL/ExtensionDerivation.lean`, `HOL/ModelExtension.lean` | proved at the history's model pair; freshness carried, not used |
| Worked typedef derivation and non-triviality of the extended model | `HOL/TypeDefDerivationExamples.lean` | proved |
| Finite semantic conservativity | `HOL/Conservativity.lean` | proved |
| Concrete non-triviality | `HOL/Concrete.lean` | proved |
| Public package integration | `HOL/Soundness.lean` and root target | proved |
| MoonBit-to-Lean refinement | no retained Typed HOL theorem | excluded |
| Syntactic extension erasure | no retained Typed HOL theorem | excluded |

## Trust basis

The retained proof line has no local `axiom`, `sorry`, or `admit`. The public
package depends on `propext`, `Classical.choice`, and `Quot.sound`, as
reported by Lean's `#print axioms`.

The old conditional and approximation modules were removed from
`formal_verification/QEDFV`. They must not be reintroduced as parallel evidence;
future work must extend the Typed HOL definitions and derivation induction.
