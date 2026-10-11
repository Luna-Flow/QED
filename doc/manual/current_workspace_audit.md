# Workspace audit (2026-10-12)

- Status: point-in-time audit
- Audience: maintainers, contributors
- Authority: stage audit; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ), current code/tests, and implementation docs
- Scope: risks, gaps, and follow-up items that still remain material on the audited baseline
- Last reviewed: 2026-10-12

_Date: 2026-10-12_

This report audits the current workspace against the repository's source-of-truth
order:

1. [QED formal specification](../attachments/qed_formal_spec.typ)
2. current code and regression tests
3. implementation-facing docs ([User manual](manual.md), [Specification conformance](conformance.md))
4. top-level summary docs (`README.md`, `application.typ`)

Validation baseline used during this audit:

- `moon test` -> pass (`357/357`)
- `formal_verification/lake build` -> pass (594 jobs)

These green gates show that the checked packages and regression suite are
internally consistent on the current baseline. The Typed HOL line now includes
constructed carriers, natural choice coherence, model-independent derivation
soundness, typed definition/specification contracts, finite extension composition,
canonical model existence, and old-language semantic transport. The remaining
formal gaps are confined to the excluded MoonBit/refinement boundary: concrete
named/De Bruijn correspondence, distinct-state provenance, and implementation
transfer.

The default `QEDFV` library target now imports only `QEDFV.HOL.Soundness` and
exports `QEDFV.HOL.typed_hol_proof_complete`. The former `Lean.Expr` proof pack
remains in the tree as archival material and is not part of the Typed HOL release
evidence.

## Resolved since the previous audit

The following previously reported risks are no longer current findings:

- type-language admissibility is now enforced at trusted theorem / sentence
  boundaries;
- connector recognition is now definition-theorem-backed rather than raw
  head-name acceptance;
- non-`bool` surface connectors now fail closed with structured errors rather
  than crashing on user-reachable paths.
- the theorem-name inventory, the `exact` / `apply` mode boundary, and the
  canonical positive / negative script corpus are now all explicit and have
  regression coverage.
- file-first `cmd` surface now exists, is covered by regression tests, and uses
  structured tactic-failure context instead of raw string-only reporting.
- the current M4 slice is now integrated on the shipped path:
  theorem-header binders, sequential block-body theorem-script parsing, raw
  binder/goal/step spans, and structured frontend diagnostics all have
  regression coverage.
- `ProofState` final theorem validation is now tightened to strict normalized
  sequent matching, with regressions that reject the old wide-match behavior.
- disjunction wrap replay now enforces the same explicit full-goal postcondition
  discipline as conjunction merge.
- local `exact` witnesses are now frozen to active hypothesis aliases only, and
  local shadowing no longer falls through to same-name theorem entries.
- canonical prover corpus and mapping-matrix coverage are now aligned with the
  hardened replay/final-theorem contracts, so `H5` no longer depends on a
  stale wider corpus contract.
- minimal `M4b` is now shipped on the main theorem-script path:
  structured branch blocks for `split` / `left` / `right` are parsed, replayed,
  covered by parser/prover/cmd regressions, and diagnosed with stable branch
  paths.

This audit therefore focuses only on the issues and gaps that still remain
material today.

## Findings

The Typed HOL semantic proof scope is closed. The findings below are retained as
implementation-boundary notes and are not evidence against the Typed HOL proof.

### [P2] The Lean line remains a paper/conformance pack, not a direct proof of the MoonBit implementation

**Why this matters**

This is not a bug in the MoonBit kernel, but it is an important status boundary
for honest communication. `lake build` proves the paper model and abstract
conformance obligations. It does not mechanically bind the current MoonBit
source tree to the Lean `Realization`.

**Evidence**

- `formal_verification/QEDFV/Engineering/Conformance.lean` reasons about abstract
  realizations and obligations;
- the traceability and rule-mapping files are paper/conformance artifacts, not a
  generated link to MoonBit symbols;
- repository docs already treat the Lean line as paper-first rather than direct
  implementation verification.

**Impact**

- public assurance language must stay precise;
- `lake build` should be read as “the stated Lean propositions and conformance
  pack compile”, not “the model is constructed”, “the pack is semantically
  closed”, or “the MoonBit program is machine-checked equivalent to Lean”.

**Required follow-up**

- keep docs precise on this boundary;
- only add a stronger claim later if a concrete MoonBit-to-Lean binding story is
  introduced as a new milestone.

**Opened task(s)**

- `A6`

## Testing gaps that still matter

The current suite is strong, but the following gaps remain important for the
next stages:

1. richer proof-block expansion beyond the current minimal branch-block slice;
2. richer hole / unfinished-proof reporting beyond the canonical unfinished case;
3. quantifier-facing frontend and its trust-relevant lowering contract;
4. any future CLI feature must continue to reuse the current positive / negative
  corpus instead of forking a second script matrix.

## Overall assessment

- The kernel and the current theorem-producing propositional subset remain in a
  materially stronger state than the previous audit snapshot described.
- This review did not uncover a direct checked-kernel soundness break in the
  current shipped path.
- The most important next work is now:
  1. keep the new structured branch-block surface on the same checked lowering /
     replay boundary;
  2. move the roadmap toward richer user-facing proof experience: script, goal,
     proof blocks, and quantifier frontend;
  3. continue corpus + docs + conformance maintenance as the frontend expands.
- The rewrite/simplify line remains research only.
- The Lean line remains green and valuable, but it should continue to be
  described as a paper/conformance pack unless a stronger implementation binding
  is explicitly added later.
