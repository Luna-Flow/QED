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
- Semantic validity preservation for all twelve typed core derivation
  constructors, including `ADD_ASSUM` and witness-based `SPECIFY`.
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

The proof does not establish growing-signature derivations, user type-constructor
syntax or semantics, object-language infinity admission,
syntactic derivation erasure for extensions, a MoonBit-to-Lean refinement, or correctness of MoonBit parsing,
elaboration, tactics, replay, mutable signature history, or theorem provenance.
Tests and engineering audits remain separate evidence for those implementation
properties.

This status supersedes older audit claims about conditional proof packs or
MoonBit conformance being part of the formal target.

## Open implementation soundness defect

[Issue #15](https://github.com/Luna-Flow/QED/issues/15) remains open. The reported
public-API reproduction reuses a theorem across sibling `KernelState` histories
whose independently allocated constant identifiers collide, deriving `|- T = F`.
`Thm` does not track state lineage, and the current admissibility checks do not
establish that the theorem belongs to the receiving declaration history.

This is a material implementation soundness defect, not just a missing proof.
The existing 357-test baseline did not cover this scenario. A green Lean build
proves the Typed HOL calculus; it cannot establish correctness of this MoonBit
behavior. Repair and implementation refinement are deferred at the user's
request. Acceptance requires rejecting the first incompatible cross-state step,
covering related registration paths, and preserving valid linear-history use.

## Remaining engineering follow-up

- Maintain checked lowering and replay as structured proof blocks expand.
- Keep hole and unfinished-proof diagnostics aligned with the canonical corpus.
- Keep quantifier-facing frontend lowering and CLI diagnostics covered.
- Keep the research rewrite/simplify path outside theorem authority.

These are implementation tasks, not additional assumptions of the Typed HOL
proof. The current cleanup changes no MoonBit implementation.
