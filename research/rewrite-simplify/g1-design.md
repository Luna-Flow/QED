# G1 Minimal Design Note: Rewrite / Simplify Pre-Research

Status: research-only
Audience: maintainers, designers
Authority: non-authoritative design note; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/governance.md`
Scope: minimum safe boundary for an isolated rewrite/simplify prototype
Last reviewed: 2026-04-16

This note implements `G1` from [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md):
define rewrite/simplify as consumers of the existing replay boundary only.

## 1. Stage Card

Goal:

- define the minimum safe contract for a future isolated rewrite/simplify
  prototype;
- keep the line strictly below the current trust boundary;
- make `G2` decision-ready without changing the shipped path.

Normative anchors:

- `doc/qed_formal_spec.pdf` / `doc/qed_formal_spec.typ`
- Appendix G `Part II Conformance Validation Scenarios`, especially:
  - rule-fidelity replay
  - boundary-fidelity
  - gate-fidelity
  - certificate non-authority
- [doc/manual.md](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/manual.md)
- [doc/conformance.md](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/conformance.md)
- [research/README.md](/Users/kcn/Desktop/repos/MoonVibe/QED/research/README.md)
- [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md)

Write boundary:

- this note only;
- future `G2` prototype code must remain in an isolated research path and must
  not alter the default shipped entrypoint.

Non-goals:

- no new `TacticStep`;
- no change to `src/tactics/proof_state.mbt`;
- no parser syntax for `rewrite`, `rw`, `simp`, or similar commands;
- no new stable theorem names;
- no new theorem authority;
- no product claim that rewrite/simplify is currently supported.

Verification commands:

```bash
moon test
cd formal_verification
lake build
```

Deliverables:

- one minimum design note with:
  - authority boundary,
  - allowed/prohibited dependencies,
  - prototype interface sketch,
  - future positive/negative cases.

## 2. Current Ground Truth

Current shipped proof scripting supports only:

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`

Current replay-critical code anchors:

- [src/logic/prop_replay.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_replay.mbt)
- [src/logic/prop_tools.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_tools.mbt)
- [src/logic/prop_refs.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_refs.mbt)
- [src/logic/prop_bool_theorems.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_bool_theorems.mbt)
- [src/tactics/proof_state.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/tactics/proof_state.mbt)

Current theorem-reference classes already present in code:

- local fact
- named theorem
- context-derived theorem

Current stable theorem-name support is proposition-oriented. It covers names such
as `imp_refl`, `truth`, `and_elim_l`, `and_elim_r`, `not_elim`, `ex_falso`,
`or_intro_l`, and `or_intro_r`. It does not currently provide a stable equality
rewrite catalog.

This matters for `G1`:

- rewrite/simplify may not assume an equality theorem-name inventory already
  exists;
- the first prototype must therefore use explicit equality witnesses rather than
  new theorem-name lookup.

## 3. Authority Contract

Rewrite/simplify is not a new proof system.

It is only allowed to do one of the following:

1. compute a candidate term or goal transformation;
2. attach an explicit replay obligation stating how the transformation would be
   reconstructed through existing checked kernel paths;
3. fail closed if such a replay obligation is not available.

It is not allowed to:

- accept a rewritten goal without a replay path;
- hide theorem construction inside parser, tactic, or CLI-only logic;
- treat certificates, traces, or metadata as theorem acceptance evidence;
- add "obvious" algebraic or logical rewrites that do not already come from a
  checked equality theorem or canonical unfold theorem.

The research line remains valid only if every successful rewrite/simplify step
can be explained as existing checked replay, not as new frontend authority.

## 4. Minimum Research Scope

`G2` must stay inside this fragment:

- proposition/equality cases only;
- no quantifiers, classes, dictionaries, or typeclass search;
- no implicit theorem search beyond the explicit witness set supplied to the
  prototype;
- no changes to the default theorem-script surface;
- no mutation of the shipped goal engine.

The prototype may inspect:

- the current goal conclusion;
- local hypotheses;
- explicit theorem witnesses passed directly to the prototype driver;
- canonical proposition connector definitions already backed by current logic
  helpers.

The prototype may transform:

- the goal conclusion;
- optionally, a selected hypothesis by index.

Hypothesis rewriting is explicitly secondary to conclusion rewriting. If the
prototype cannot preserve honest hypothesis accounting through existing replay
helpers, it must support conclusion rewriting only and reject hypothesis
rewrites.

## 5. Allowed Dependency Set

The prototype may depend only on existing checked kernel and logic replay
building blocks.

Allowed helper classes:

- canonical proposition unfold helpers:
  - `logic_prop_unfold_head`
  - `logic_prop_unfold_not`
  - `logic_prop_unfold_imp`
  - `logic_prop_unfold_and`
  - `logic_prop_unfold_or`
- equality/congruence helpers:
  - `logic_apply_fun_eq`
  - `logic_apply_fun_eq2`
  - `logic_eq_sym`
  - `logic_eq_mp_bool`
- beta normalization helpers:
  - `logic_beta_normalize_eq`
  - `logic_normalize_prop_beta`
  - `logic_beta_nf_bool_term`
  - `logic_beta_nf_bool_term_deep`
- proposition replay helpers:
  - `logic_prop_ensure_sequent`
  - `logic_prop_strengthen_to_hyps`
  - `logic_prop_discharge_imp_prefix`
  - `logic_prop_replay_imp_elim_backward`
  - `logic_prop_replay_imp_elim_backward_thm`
  - `logic_prop_merge_conjunction`
  - `logic_prop_or_wrap_left`
  - `logic_prop_or_wrap_right`
- existing checked kernel-facing logic wrappers already used by `src/logic/`.

Explicitly prohibited dependencies:

- new primitive rules;
- ad-hoc theorem fabrication inside `tactics`, `parser`, `prover`, or a
  research driver;
- theorem acceptance based on certificates or traces alone;
- a new global rewrite database with undocumented applicability;
- default-path registration in `src/tactics/`, `src/prover/`, or parser syntax.

## 6. Witness Model

Because there is no shipped equality theorem-name catalog today, the minimum
prototype witness model is:

```text
RewriteWitness =
  | LocalEquality(name)
  | ExplicitTheorem(thm)
  | CanonicalUnfold(connector)
  | BetaNormalization
```

Notes:

- `LocalEquality(name)` means a local hypothesis whose term is checked to be an
  equality before use.
- `ExplicitTheorem(thm)` is research-only. It is not a stable public API and is
  only for isolated prototype driving.
- `CanonicalUnfold(connector)` is limited to current proposition connectors
  already backed by canonical definition theorems.
- `BetaNormalization` is limited to the existing normalization helpers.

No other witness source is allowed in `G2`.

## 7. Prototype Interface Sketch For G2

The isolated prototype should expose internal research interfaces with the
following shape:

```text
RewriteDirection =
  | LeftToRight
  | RightToLeft

RewriteTarget =
  | GoalConcl
  | GoalHyp(index)

RewriteSiteStep =
  | CombFun
  | CombArg
  | AbsBody

RewriteRequest = {
  target: RewriteTarget,
  witness: RewriteWitness,
  direction: RewriteDirection,
  site: Array[RewriteSiteStep]
}

ReplayStepKind =
  | ResolveWitness
  | Symmetry
  | Congruence
  | Unfold
  | BetaNormalize
  | EqMpBool

ReplayObligation = {
  before_hyps,
  before_concl,
  after_hyps,
  after_concl,
  steps: Array[ReplayStepKind]
}

RewriteOutcome =
  | Rewritten(after_goal, obligation)
  | NoChange
  | HonestFailure(reason)
```

Contract:

- the prototype may compute `after_goal` syntactically;
- it may return `Rewritten` only when it also constructs a replay obligation
  from the allowed dependency set;
- if the obligation cannot be stated concretely before returning, the result
  must be `HonestFailure`.

These interfaces are research-only and must not appear in a shipped public
package surface during `G2`.

## 8. Rewrite Contract

The first rewrite contract is deliberately narrow.

Input requirements:

- the target site must be explicit;
- the direction must be explicit;
- the witness must already be resolved;
- the witness conclusion must be an equality, unless the witness kind is
  `CanonicalUnfold` or `BetaNormalization`.

Success requirements:

- the rewrite result must preserve typing under the existing checked path;
- the replay obligation must use only the allowed helper set;
- if the target is proposition-typed and the result is used to transport a proof
  of truth, the final transport must go through existing boolean equality replay
  such as `logic_eq_mp_bool`.

Failure requirements:

- unknown local witness name;
- witness is not an equality theorem;
- rewrite site does not match the witness side chosen by direction;
- congruence reconstruction is unavailable through the allowed helper set;
- beta/unfold normalization changes are not replayable on the current term
  shape.

All such failures must be reported as honest research failures, not silently
reinterpreted.

## 9. Simplify Contract

`simplify` is not a separate reasoning engine. It is a bounded strategy that
sequences a small set of already-replayable steps.

Initial simplify scope:

1. canonical unfold of current proposition connectors;
2. beta normalization;
3. optional explicit equality rewrites from the caller-provided witness set;
4. beta normalization again if needed.

Initial simplify restrictions:

- no theorem search beyond the witness set;
- no recursive context theorem mining;
- no automatic import of future theorem catalog entries;
- no rewriting under binders beyond what the explicit replay plan can justify.

Termination rule:

- every simplify pass must use an explicit step bound;
- on bound exhaustion it must return `HonestFailure` or `NoChange`, never loop.

## 10. Promotion Constraints For G2

Before any prototype code is written, these constraints are fixed:

- prototype code stays outside the shipped path;
- no changes to current parser syntax;
- no edits to `ProofState` dispatch to make the prototype work;
- no default theorem-name resolution for equality;
- no public API stabilization;
- no status-doc update claiming support.

If the prototype later needs any of the above, it has exceeded `G2` and must
stop for re-review before proceeding.

## 11. Required Future Cases

Positive cases the prototype should be able to demonstrate:

- rewrite the goal conclusion with a local equality witness;
- rewrite the goal conclusion with an explicit theorem witness;
- simplify a proposition term by canonical unfold plus beta normalization;
- if hypothesis rewriting is attempted, rewrite one selected hypothesis without
  changing theorem authority.

Negative cases the prototype must reject honestly:

- non-equality theorem used as a rewrite witness;
- missing local witness;
- direction/site mismatch;
- rewrite that would require implicit theorem invention;
- simplify step that depends on theorem search outside the provided witness set;
- any path that cannot be explained as existing checked replay.

## 12. Go / No-Go Signal

The desired outcome of `G1` is not "rewrite exists".

The desired outcome is:

- a future prototype can be built without expanding the trust boundary;
- if that stops being true, the line remains research-only and does not enter
  the shipped path.

That is the only acceptable baseline for `G2`.
