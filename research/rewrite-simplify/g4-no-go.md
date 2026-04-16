# G4 Go/No-Go Conclusion: Rewrite / Simplify

Status: research-only
Audience: maintainers, designers
Authority: non-authoritative research conclusion; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/governance.md`
Scope: go/no-go conclusion for rewrite/simplify promotion on the audited baseline
Last reviewed: 2026-04-16

Current conclusion: `No-Go` for promotion on the 2026-04-05 baseline. The line
remains research only and stays off the default shipped product path.

This note implements `G4` from [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md):
publish the final go/no-go conclusion for the current rewrite/simplify
research line.

## 1. Stage Card

Goal:

- decide whether the current rewrite/simplify line may be promoted beyond the
  isolated research boundary;
- publish one explicit conclusion tied to the promotion gates from `G3`;
- keep the result maximally faithful to the current proof-authority boundary.

Normative anchors:

- `doc/qed_formal_spec.pdf` / `doc/qed_formal_spec.typ`
- Part II Appendix G conformance obligations:
  - rule-fidelity replay
  - boundary-fidelity
  - gate-fidelity
  - certificate non-authority
- [PLAN.md](/Users/kcn/Desktop/repos/MoonVibe/QED/PLAN.md)
- [research/rewrite-simplify/g1-design.md](/Users/kcn/Desktop/repos/MoonVibe/QED/research/rewrite-simplify/g1-design.md)
- [research/rewrite-simplify/g3-promotion-gates.md](/Users/kcn/Desktop/repos/MoonVibe/QED/research/rewrite-simplify/g3-promotion-gates.md)

Write boundary:

- this note only;
- no changes to `src/logic`, `src/tactics`, `src/prover`, `src/parser`,
  `src/cmd`, or the default shipped product path.

Non-goals:

- no promotion into a shipped tactic;
- no new parser or command surface for rewrite/simplify;
- no capability-inventory changes in `logic`;
- no attempt to reinterpret research-only constructors as stable public API;
- no weakening of the kernel-first trust boundary.

Verification commands:

```bash
moon test
cd formal_verification
lake build
```

Deliverables:

- one go/no-go conclusion note with:
  - the exact evidence checked for `G4`,
  - gate-by-gate promotion judgment,
  - the final promotion decision,
  - the minimum changes required before reconsideration.

## 2. Evidence Checked For This Conclusion

This conclusion was checked against the current repository state on
2026-04-05.

Inputs required by `G3` and verified here:

1. the `G1` minimum design note;
2. the `G3` promotion-gates note;
3. the current `G2` isolated prototype and its package tests:
   - [src/research_rewrite/research_rewrite.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/research_rewrite/research_rewrite.mbt)
   - [src/research_rewrite/research_rewrite_test.mbt](/Users/kcn/Desktop/repos/MoonVibe/QED/src/research_rewrite/research_rewrite_test.mbt)
4. the current full verification gates:
   - `moon test` -> passed (`270/270`)
   - `formal_verification/lake build` -> passed
5. the current promoted-surface search in:
   - `src/logic`
   - `src/tactics`
   - `src/prover`
   - `src/parser`
   - `src/cmd`

Current observed facts:

- the research package still owns the rewrite witness, site, request, and
  replay-obligation vocabulary;
- the research package still exposes research-only constructors such as
  `research_explicit_theorem`;
- no shared rewrite/simplify capability contract exists in the shipped
  `logic`/`tactics` coordination model;
- no tactic/prover/parser/cmd integration path currently promotes the research
  result into real theorem-synthesis closure.

## 3. Gate-By-Gate Judgment

### Gate A: Replayability

Judgment: not sufficient for promotion.

Reason:

- the current prototype succeeds only when it can build and self-check replay
  obligations, which is mathematically aligned with `G1`;
- however, promotion requires a concrete path from rewrite behavior into real
  theorem-producing closure, not only a research-time obligation validator;
- that integration still does not exist in the shipped tactic/prover flow.

Conclusion:

- the current research package demonstrates replay discipline;
- it does not yet satisfy the stronger promotion requirement.

### Gate B: Trust Boundary

Judgment: not sufficient for promotion.

Reason:

- the current line remains safe because it is isolated and off the shipped
  path;
- promotion requires the same discipline to survive after entering shared
  logic/tactic layers;
- no promoted design has yet shown that rewrite/simplify can enter those
  layers without widening authority or relying on research-only acceptance
  checks.

Conclusion:

- the trust boundary is currently preserved by isolation;
- promotion is not yet justified by a promoted boundary design.

### Gate C: Capability-Model Compatibility

Judgment: fail.

Reason:

- the shipped `B/C` model already uses explicit capability organization in
  `logic` for exact/apply behavior;
- rewrite/simplify still lives in a private research vocabulary with no shared
  `logic` inventory for applicability, failure modes, or witness classes;
- promoting now would bypass the existing coordination model rather than extend
  it honestly.

Conclusion:

- no promotion is allowed while rewrite capability remains research-private.

### Gate D: Test Coverage

Judgment: fail for promotion readiness.

Reason:

- the current repository verification gates are green, and the isolated
  research package has positive and negative regressions;
- but the promotion gate requires coverage at the level of the promoted
  surface;
- there is still no tactic-level, prover-level, parser-level, or command-level
  rewrite acceptance coverage because no such promoted surface exists.

Conclusion:

- current tests are enough to trust the research claim;
- they are not enough to justify shipping or promotion.

### Gate E: Surface Contract

Judgment: fail.

Reason:

- the only available inputs are still research-only constructors and internal
  request types;
- no stable witness-input contract exists for a user-facing tactic or command
  surface;
- `ExplicitTheorem(Thm)` remains acceptable for isolated research driving but
  is not an honest shipped contract.

Conclusion:

- there is no promotion-ready public surface.

## 4. Final Decision

Final decision: `No-Go`.

The current rewrite/simplify line must remain research only.

This conclusion is required by the current mathematical and engineering facts:

- there is still no shared capability contract in `logic`;
- there is still no promoted surface outside `research_*` APIs;
- there is still no demonstrated path from rewrite behavior into real
  theorem-synthesis closure;
- the current safety story depends on isolation, not on a completed promoted
  design.

Therefore:

- do not promote rewrite/simplify into `src/tactics`;
- do not add parser or command claims for rewrite/simplify support;
- do not describe the current prototype as shipped capability;
- keep the line isolated until the missing contracts are built and verified.

## 5. Required Changes Before Reconsideration

Promotion may be reconsidered only after all of the following are true:

1. a shared rewrite/simplify capability contract exists in `logic`, with
   explicit witness classes, applicability rules, and honest failure semantics;
2. tactic/prover integration shows how successful rewrite steps participate in
   final theorem synthesis without introducing new theorem authority;
3. a stable user-facing surface contract exists outside the research package;
4. promoted-surface tests exist at the exact integration level being claimed;
5. the promoted scope is documented narrowly and still fails closed on
   unsupported paths.

Until then, the correct status is:

- useful research result;
- valid isolated prototype;
- not promotion-ready.
