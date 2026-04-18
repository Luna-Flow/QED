# Current Workspace Audit

Status: point-in-time audit
Audience: maintainers, contributors
Authority: stage audit; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and implementation docs
Scope: risks, gaps, and follow-up items that still remain material on the audited baseline
Last reviewed: 2026-04-16

_Date: 2026-04-05_

This report audits the current workspace against the repository's source-of-truth
order:

1. `doc/qed_formal_spec.pdf` / `doc/qed_formal_spec.typ`
2. current code and regression tests
3. implementation-facing docs (`doc/manual.md`, `doc/conformance.md`)
4. top-level summary docs (`README.md`, `application.typ`)

Validation baseline used during this audit:

- `moon test` -> pass (`276/276`)
- `formal_verification/lake build` -> pass

These green gates show the workspace is internally consistent on the current
baseline. They do not by themselves mean that every planned product capability
is already shipped.

## Resolved Since The Previous Audit

The following previously reported risks are no longer current findings:

- type-language admissibility is now enforced at trusted theorem / sentence
  boundaries;
- connector recognition is now definition-theorem-backed rather than raw
  head-name acceptance;
- non-`bool` surface connectors now fail closed with structured errors rather
  than crashing on user-reachable paths.
- theorem-name inventory、`exact` / `apply` mode boundary，以及 canonical
  positive / negative script corpus 现在都已显式化并有回归覆盖。
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

This audit therefore focuses only on the issues and gaps that still remain
material today.

## Findings

### [P1] Theorem-script body is still limited to the current sequential `by` forms

**Why this matters**

The current parser and prover surface is honest and tested, and theorem-header
binders are now shipped. The next real frontend milestone is still unshipped:
structured branch blocks for the existing `split` / `left` / `right` tactics.

**Evidence**

- `parse_theorem_script_raw` currently accepts only sequential `by` bodies:
  single-line `theorem ... := by step; step; ...` or a newline-separated block
  body with the same step semantics;
- no shipped syntax exists yet for structured branch blocks;
- parser-side public utilities such as `parse_let` / `parse_def_function` remain
  outside the main theorem-script product path.

**Impact**

- natural proof authoring remains limited;
- diagnostics are already better, but the user-facing proof surface is still the
  smaller sequential slice.

**Required follow-up**

- keep all new syntax on the same checked lowering boundary;
- add only the minimum `M4b` surface first: structured blocks for existing
  branch tactics, not a general proof-language expansion.

**Opened task(s)**

- `F5`
- `F6`
- `F7`
- `C6`
- `D6`
- `E5`
- `E6`
- `H6`

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
- `lake build` should be read as “spec/conformance pack is closed”, not “the
  MoonBit program is machine-checked equivalent to Lean”.

**Required follow-up**

- keep docs precise on this boundary;
- only add a stronger claim later if a concrete MoonBit-to-Lean binding story is
  introduced as a new milestone.

**Opened task(s)**

- `A6`

## Testing Gaps That Still Matter

The current suite is strong, but the following gaps remain important for the
next stages:

1. structured branch-block parser/prover/cmd regressions, including nested
   diagnostic paths;
2. any future CLI feature must continue to reuse the current positive / negative
   corpus instead of forking a second script matrix.

## Overall Assessment

- The kernel and the current theorem-producing propositional subset remain in a
  materially stronger state than the previous audit snapshot described.
- This review did not uncover a direct checked-kernel soundness break in the
  current shipped path.
- The most important next work is now:
  1. `H5` integration of the hardened baseline;
  2. `M4b` structured branch blocks on top of that hardened baseline.
- The rewrite/simplify line remains research only.
- The Lean line remains green and valuable, but it should continue to be
  described as a paper/conformance pack unless a stronger implementation binding
  is explicitly added later.
