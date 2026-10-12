# Workspace audit (2026-10-12)

- Status: Typed HOL is the sole formal proof line.
- Authority: [QED Typed HOL Core](../attachments/qed_formal_spec.typ).
- Scope: Typed HOL proof status and material implementation risks.
- Excluded: MoonBit implementation refinement and user-facing proof workflow.

The former approximate Lean proof tree has been removed. The current formal
library contains only the intrinsically typed development under
`formal_verification/QEDFV/HOL`; the root module imports its public
`Soundness` entry point. The library builds with `lake build`.

## Verified results

- Intrinsic simple types and De Bruijn terms, with typed renaming, substitution,
  beta, and type-instantiation evaluation laws.
- Semantic validity preservation for all thirteen derivation constructors,
  including `ADD_ASSUM`, witness-based `SPECIFY`, and infinity admission.
- Object-language truth, falsity, conjunction, implication, universal and
  existential quantification with proved evaluation characterizations.
- The closed infinity sentence is valid in every model; its derivation
  constructor has a direct soundness case.
- Derivation soundness by induction, for every constant interpretation.
- History-indexed definition and specification derivations. A specification
  witness is derived at the preceding history; soundness composes over fresh
  constant IDs in the fixed signature.
- Semantic extension contracts and witnessed predicate subtype carrier laws.
- Old-language semantic validity equivalence over finite modeled extension
  sequences.
- A concrete interpretation in which `succ(0) = 0` is false and therefore
  underivable.

The public theorem is `QEDFV.HOL.typed_hol_core_proof_complete`. Audited
`#print axioms` output is `propext`, `Classical.choice`, and `Quot.sound`.
There are no project-defined axioms, `sorry`, or `admit` in the retained Lean
tree.

## Boundaries

The proof does not establish growing-signature derivations, a history-indexed full
calculus that chains the derived type-definition laws with core rules (the laws are
derivation conclusions at the extended history and sound at its model pair, and
history freshness is carried but unused by soundness), the MoonBit infinity
registration gate, syntactic derivation erasure for extensions, or a
MoonBit-to-Lean refinement.
Parser, elaborator, tactic, replay, and mutable-state behavior remain separate
implementation evidence. The MoonBit theorem-provenance condition in issue #15
is now enforced independently by the kernel and covered by regression tests.

This status supersedes older audit claims about conditional proof packs or
MoonBit conformance being part of the formal target.

## Issue #15 implementation repair

[Issue #15](https://github.com/Luna-Flow/QED/issues/15) is repaired in the
current implementation work. Every theorem carries the declaration lineage at
which it was first admitted, and admissibility requires that lineage to be a
prefix of the receiving state's history. Sibling histories therefore reject a
theorem before constant-id reuse can combine incompatible declarations, while
linear descendants continue to accept inherited theorems. Infinity-anchor,
typedef, and specification registration also reject sibling witnesses.

The repair is an independently tested MoonBit invariant, not a MoonBit-to-Lean
refinement theorem. The Typed HOL build still certifies only the formal calculus
and its stated fixed-signature extension results.

## Remaining engineering follow-up

- Maintain checked lowering and replay as structured proof blocks expand.
- Keep hole and unfinished-proof diagnostics aligned with the canonical corpus.
- Keep quantifier-facing frontend lowering and CLI diagnostics covered.
- Keep the research rewrite/simplify path outside theorem authority.

These are implementation tasks, not additional assumptions of the Typed HOL
proof. The current work records the issue #15 invariant and the MoonBit 0.10.15
compatibility check without extending the Lean proof boundary.
