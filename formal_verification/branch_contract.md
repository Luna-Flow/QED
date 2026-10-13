# QED formal branch contract

- Status: active research contract
- Audience: formalization contributors, kernel maintainers, reviewers
- Authority: [`qed_formal_spec.typ`](../doc/attachments/qed_formal_spec.typ)
- Scope: promotion order for mathematical verification and the later implementation correspondence
- Boundary: this file defines gates; it is not a logical axiom and does not certify the executable kernel
- Last reviewed: 2026-10-14

The branches form a dependency order. A later branch may use an earlier result
only after the earlier promotion gate passes. A test, an abstract theorem or a
documentation statement cannot satisfy a missing correspondence gate.

## Promotion order

| Branch | Evidence anchor | Published claim | Promotion gate |
| --- | --- | --- | --- |
| `HOL/Core` | `QEDFV/HOL/Types.lean`, `Terms.lean`, `Evaluation.lean`, `Rules.lean`, `Derivation.lean` | The intrinsically typed core rules, choice and the exact infinity sentence are semantically sound | Lean build and axiom audit pass; no project `axiom`, `sorry` or `admit` |
| `HistoryModel` | `ModelExtension.lean`, `TypeDefGate.lean`, `ExtensionDerivation.lean` | Definition, specification and type-definition products have local laws and old-language transport over a fixed total signature | Preceding-history witnesses, locality and old-language conditions are explicit |
| `HistoryClosure` | `HistoryDerivation.lean`, `HistoryDerivationExamples.lean`, `HistoryAuditExamples.lean` | Extension products compose with every supported core rule at one fixed history | Soundness, non-vacuity, invalid-witness and freshness negative checks pass |
| `GrowingSignature/Allocation` | `DeclarationAllocation.lean`, `DeclarationAllocationExamples.lean` | Finite fresh allocation preserves old entries and compatibility with a fixed total signature | Constructor allocation, signature embeddings and model transport are proved before promotion |
| `Refinement/MoonBit` | planned | MoonBit representations, state transitions and theorem constructors correspond to the Typed HOL objects | Per-constructor representation, typing, evaluation, acceptance and state lemmas are checked |
| `IndependentChecker` | planned | Explicit derivation certificates can be validated without calling MoonBit theorem constructors | Certificate syntax, malformed corpus, statement/history binding, checker soundness and deterministic replay pass |

## Evidence rules

The branch names are architectural labels, not status values. The status of each
obligation lives in the machine-readable obligation registry (introduced with
the verification tooling). Keep the following claims separate:

- fixed-signature semantic validity;
- history-indexed derivation soundness;
- growing-signature transport;
- MoonBit implementation correspondence;
- syntactic extension erasure.

In particular, the current kernel snapshot and lineage repairs are tested
implementation invariants. They do not promote `Refinement/MoonBit`.

## Next gate

The first unclosed promotion is `GrowingSignature/Allocation`. The next Lean
increment must define state embeddings and transport for declarations, types,
contexts, terms, evaluation and validity before a growing-history derivation is
introduced. Type-definition erasure remains a separate relativisation project.
