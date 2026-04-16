# G3 Promotion Gates: Rewrite / Simplify

Status: research-only
Audience: maintainers, designers
Authority: non-authoritative research gate note; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/governance.md`
Scope: promotion criteria for rewrite/simplify research, not shipped behavior
Last reviewed: 2026-04-16

This note implements `G3` from [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md):
define the promotion gates for turning the current rewrite/simplify research
line into a real tactic candidate.

## 1. Normative Anchors

Primary anchors:

- `doc/qed_formal_spec.pdf` / `doc/qed_formal_spec.typ`
- Part II Appendix G conformance obligations:
  - rule-fidelity replay
  - boundary-fidelity
  - gate-fidelity
  - certificate non-authority
- [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md)
- [research/rewrite-simplify/g1-design.md](/Users/kcn/Desktop/repos/MoonVibe/QED/research/rewrite-simplify/g1-design.md)

Current implementation anchors used for this assessment:

- [src/research_rewrite/research_rewrite.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/research_rewrite/research_rewrite.mbt)
- [src/logic/prop_catalog.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_catalog.mbt)
- [src/logic/prop_refs.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/prop_refs.mbt)

Current stage boundary:

- `G3` defines promotion criteria and records current gaps.
- `G3` does not change the shipped path.
- `G3` does not itself decide promotion.
- `G4` will use this note to publish the final go/no-go conclusion.

## 2. Promotion Gates

### Gate A: Replayability

Promotion requirement:

- every promoted rewrite/simplify success path must be explainable as explicit
  replay through existing checked kernel/logic helpers;
- the promoted surface must have a concrete closure story into real
  theorem-producing flow, not only a research-time candidate conclusion
  transform;
- the proof-producing boundary must remain `kernel`, with promoted logic/tactic
  layers acting only as replay/orchestration layers.

Required evidence:

- successful paths replay via existing checked helpers such as congruence,
  symmetry, unfold, beta normalization, and boolean equality transport;
- proof-state or prover integration demonstrates that the promoted tactic can
  participate in final `Thm` reconstruction rather than stopping at research
  metadata;
- failure paths remain honest and fail closed.

Promotion blocker examples:

- a rewrite path that depends on a step not recoverable from existing checked
  helpers;
- a tactic surface that rewrites the current goal but cannot connect the result
  back into the final replay closure;
- using replay-obligation metadata itself as proof acceptance evidence.

### Gate B: Trust Boundary

Promotion requirement:

- no new primitive-rule authority;
- no new theorem-construction boundary outside `src/kernel`;
- no use of certificates, traces, or UI-layer artifacts as theorem acceptance
  evidence.

Required evidence:

- promotion design can still be described as organization or replay of existing
  checked paths;
- the tactic/prover layer does not fabricate equality theorems or shortcut
  kernel checks;
- unsupported rewrite cases stay fail closed.

Promotion blocker examples:

- adding a rewrite engine that can conclude term equality without a checked
  theorem witness or canonical definition theorem;
- letting parser/tactic/prover directly certify a rewritten goal as solved;
- expanding the research package into a second theorem authority.

### Gate C: Capability-Model Compatibility

Promotion requirement:

- rewrite/simplify must align with the current `B/C` capability model rather
  than introducing a private research-only classification;
- applicability, failure modes, and required evidence must be expressible in a
  shared inventory model comparable to the current theorem-catalog classes;
- any promoted equality or rewrite witness contract must have a stable place in
  the same logic/tactic coordination story as existing exact/apply resolution.

Current compatibility anchor:

- `logic` already classifies theorem-backed capabilities via
  `PropTheoremClass` and `PropTheoremEntry`, with explicit `exact_class` and
  `apply_class`;
- `logic_prop_resolve_exact_theorem` and `logic_prop_resolve_apply_theorem`
  encode mode-specific capability resolution and honest unavailability.

Required evidence:

- rewrite/simplify promotion either reuses this shared inventory model or adds a
  similarly explicit companion model inside `logic`, not inside the research
  package;
- each promoted witness source has documented applicability shape and honest
  failure behavior;
- tactic integration does not need ad-hoc special cases that bypass the shared
  capability boundary.

Promotion blocker examples:

- keeping witness classification only inside `src/research_rewrite/`;
- relying on raw research constructor APIs with no mapping to logic/tactic
  capability inventory;
- promoting a tactic whose availability semantics are only “try it and see”.

### Gate D: Test Coverage

Promotion requirement:

- positive, negative, and boundary regressions must exist for every promoted
  capability class;
- coverage must exist at the level where the feature is promoted, not only at
  lower research layers.

Minimum evidence for promotion:

- package-level rewrite/simplify tests covering:
  - local equality
  - explicit theorem witness
  - canonical unfold
  - beta normalization
  - site mismatch
  - unsupported binder path
  - step-limit behavior
  - honest failure
- tactic/prover/script-level tests if the feature is promoted into those layers;
- whole-workspace `moon test` and `formal_verification/lake build`.

Promotion blocker examples:

- only having term-conclusion tests while claiming tactic-level readiness;
- lacking negative regressions for unsupported binder/hypothesis paths;
- lacking a corpus mapping from promoted rewrite behavior back to the shared
  capability model.

### Gate E: Surface Contract

Promotion requirement:

- the user-facing input contract must be explicit before promotion;
- research-only constructors and driver helpers must not silently become the
  shipped API surface;
- the promoted surface must state what witnesses it accepts, how sites are
  specified, and how failures are reported.

Required evidence:

- a stable witness-input story, for example a documented theorem-name inventory,
  local-equality contract, or another explicit shared surface defined outside
  the research package;
- a documented tactic/command/input shape if promotion targets `tactics`,
  `parser`, or `cmd`;
- removal or continued non-shipped status of research-only APIs such as
  `research_explicit_theorem` if they are not suitable for user-facing use.

Promotion blocker examples:

- trying to promote `ExplicitTheorem(Thm)` as a user-facing contract;
- shipping rewrite/simplify without a documented witness source policy;
- promoting internal `research_*` helper APIs as if they were stable product
  surface.

## 3. Non-Blocking Extensions

The following are explicitly not required for first promotion:

- hypothesis rewrite;
- `AbsBody` rewrite;
- theorem search beyond explicit witnesses;
- richer simplify heuristics;
- parser syntax such as `rw` or `simp`.

These may remain unavailable while a narrower first promoted surface ships, as
long as unsupported paths fail honestly and the promoted scope is stated
precisely.

## 4. Current G2 Gap Assessment

Assessment target:

- the isolated research package in
  [src/research_rewrite/research_rewrite.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/research_rewrite/research_rewrite.mbt)
  and its current tests.

Status matrix:

| Gate | Current G2 status | Assessment |
| --- | --- | --- |
| Replayability | conclusion-only rewrite/simplify paths build and self-check replay obligations | Pass with restriction |
| Trust boundary | remains isolated and off the shipped path; no new theorem authority introduced | Pass with restriction |
| Capability-model compatibility | no shared logic/tactic inventory for rewrite capability yet | Fail |
| Test coverage | research package has positive/negative regressions and workspace gates are green | Pass with restriction |
| Surface contract | current inputs are research-only helper constructors, not a promoted product contract | Fail |

Detailed assessment:

### Replayability: Pass with restriction

What is already true:

- current `G2` only succeeds on paths that it can reconstruct through existing
  checked helpers;
- current tests verify replay-obligation consistency for supported success
  cases;
- unsupported paths such as binder-body rewriting still fail honestly.

What is still missing:

- there is no proof-state or prover integration path from the research result
  into final theorem synthesis;
- `research_validate_replay_obligation` is a research self-check, not a shipped
  acceptance boundary;
- current scope is still conclusion-only.

Current blocker to promotion:

- no demonstrated integration into real tactic/prover closure.

### Trust boundary: Pass with restriction

What is already true:

- the research package is isolated;
- the shipped path is untouched;
- success cases still depend on existing checked logic/kernel helpers.

What is still missing:

- promotion would require a documented integration story showing that the same
  discipline survives outside the research package;
- current research constructors remain public inside the research package and
  therefore still need a promotion-time surface review.

Current blocker to promotion:

- trust boundary is currently preserved by isolation, not yet by a promoted
  design inside shared logic/tactic layers.

### Capability-model compatibility: Fail

What is already true:

- the logic line now has an explicit theorem catalog and mode-specific exact/apply
  resolution model;
- equality-related theorem entries already exist in the theorem catalog.

What is still missing:

- rewrite/simplify does not yet map to a shared capability inventory in
  `logic`;
- there is no stable classification for rewrite witness applicability,
  unavailability, or mode restrictions comparable to the current exact/apply
  model;
- the research package still owns its own witness/site/replay vocabulary.

Current blocker to promotion:

- no shared `logic`/`tactics` capability contract for rewrite behavior.

### Test coverage: Pass with restriction

What is already true:

- G2 package-level tests cover positive and negative cases;
- current full-workspace gates are green.

What is still missing:

- there is no tactic-level or script-level acceptance coverage;
- there is no mapping matrix from rewrite capability to future promoted user
  surface;
- there is no evidence yet that promotion would integrate cleanly with the
  canonical script corpus.

Current blocker to promotion:

- coverage stops at the research package boundary.

### Surface contract: Fail

What is already true:

- the research package exposes explicit constructors and requests, which is
  enough for internal prototyping.

What is still missing:

- no stable user-facing witness-input contract;
- no parser/tactic/cmd syntax or other promoted entrypoint;
- `research_explicit_theorem` is unsuitable as a product-facing contract.

Current blocker to promotion:

- no promotion-ready public surface exists yet.

## 5. Required Evidence For G4

Before `G4` publishes the final go/no-go conclusion, it must check:

1. this `G3` note and the `G1` minimum design note;
2. current `G2` package tests and their exact supported scope;
3. current full verification gates:
   - `moon test`
   - `cd formal_verification && lake build`
4. whether a real promotion target surface now exists:
   - `logic` inventory addition,
   - `tactics` integration,
   - `parser`/`cmd` input contract,
   - or none;
5. whether rewrite capability has been mapped into the shared `B/C` capability
   model rather than remaining research-private;
6. whether tactic/prover integration now closes the replayability gap.

`G4` should conclude `No-Go` if any of the following remains true:

- rewrite/simplify still lacks a shared capability contract in `logic`;
- the only available surface is still `research_*` APIs;
- there is still no path from promoted rewrite behavior into real theorem
  synthesis closure;
- promotion would require widening the trust boundary.

`G4` may conclude `Go` only if all hard gates pass and the promoted scope is
stated narrowly and honestly.
