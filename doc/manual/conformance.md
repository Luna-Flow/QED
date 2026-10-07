# Specification conformance

- Status: active
- Audience: contributors, reviewers
- Authority: engineering conformance guide; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ) and current code/tests
- Scope: code/test mapping, implementation alignment, contributor obligations, and documentation example rules
- Last reviewed: 2026-04-20

This document records how the current MoonBit engineering line aligns with [QED formal specification](../attachments/qed_formal_spec.typ),
and what peripheral engineering must do to conform to the current core.

It is not a new normative layer; its role is to put "paper requirements", "current code", "current
tests", and "peripheral engineering obligations" on the same table.

## Normative source

QED's current authority relations are as follows:

- [QED formal specification](../attachments/qed_formal_spec.typ) is the only normative source.
- [`doc/attachments/qed_formal_spec.typ`](../attachments/qed_formal_spec.typ) is the specification source file.
- Current code and tests determine the actual current shipped state.
- [Documentation governance](governance.md) defines the documentation hierarchy and citation rules.
- [User manual](manual.md) describes the implementation contract in the current repository.
- This document describes engineering conformance, the code/test mapping, and the contributor checklist.

The Lean anchors for Part II conformance are mainly in:

- `formal_verification/QEDFV/Engineering/Conformance.lean`
- `formal_verification/QEDFV/Spec/Items.lean`
- `formal_verification/QEDFV/Audit/AppendixG.lean`
- `formal_verification/QEDFV/Audit/PartI.lean`

## Implemented vs not implemented

### Implemented and tested

The parts currently backed by stable code and regression tests are:

- typed term/type core
- opaque theorem object + checked primitive rules
- scoped signature stack and definition history discipline
- `DefOK` / `TypeDefOK` / `SpecOK` gate
- theorem admissibility around const identity, schema instance, definitional coherence, and
  type-language admissibility
- resolved elaboration boundary with frozen constant identity
- parser normalize + raw-offset contract
- parser-owned goal lowering boundary without direct tactics dependency
- basis-backed lowering contract for surface connectors
- canonical definition-theorem-backed connector recognition
- audit certificates and executable conservative replay hook
- definition theorem / unfold / replay helpers in the logic layer
- supported propositional theorem scripting paths that replay to kernel `Thm`

### Implemented but intentionally partial

The following parts exist, but their coverage is still limited:

- `Goal` / `ProofState` / step execution and the `ps_qed` success path in `tactics`
- the theorem-script driver in `prover`
- theorem-name based replay currently covers only a small catalog of stable propositions
- the parser currently supports theorem-header binders, sequential `by` bodies, and a minimal
  structured branch block syntax:
  a theorem header may carry zero or more `(name : type)` binders;
  the body may be written as a single line `theorem ... := by step; step; ...`,
  or as a block `theorem ... := by` followed by a newline-separated list of steps;
  `split` / `left` / `right` may still carry the minimal branch block syntax, and the parser keeps
  raw binder/goal/step spans; the actual scheduling and blame attribution of branch bodies is
  handled by `prover`
- theorem-script also currently supports the `hole` / `hole <name>` unfinished-proof step;
  theorem-header binders now form a shipped quantifier-facing surface that reliably enters
  goal lowering, proof-state locals, and cmd diagnostics; a raw `forall` / `∀`
  theorem goal also enters the shipped lowering path as goal-only sugar, but is still not
  term-level syntax
- parser-side `parse_let` / `parse_def_function` are formalized as a non-script utility surface

These layers are not a complete frontend in which "any user proof can produce a trusted theorem".

### Not implemented

The following are currently not implemented and should be treated explicitly as missing capabilities:

- richer proof blocks
- promoted rewrite/simplify tactic / command surface
- dictionary passing
- typeclass frontend
- instance environment / instance search
- constraint solving
- metavariables / holes
- local type inference
- higher-order unification
- complete theorem reconstruction for arbitrary scripts / arbitrary tactic combinations

## Code and test mapping

| Area | Current implementation | Regression coverage |
| --- | --- | --- |
| Typed core + boundary conversion | `src/kernel/types.mbt`, `src/kernel/terms.mbt` | `src/kernel/kernel_terms_test.mbt`, `src/kernel/kernel_types_test.mbt` |
| Scoped state + extension gates | `src/kernel/sig.mbt` | `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Primitive rules + admissibility | `src/kernel/thm.mbt` | `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Resolved elaboration boundary | `src/elab/resolved.mbt` | `src/elab/elab_test.mbt` |
| Parser bridge + normalize/raw-offset contract | `src/parser/parser.mbt` | `src/parser/parser_test.mbt` |
| Parser-to-tactics explicit goal bridge | `src/parser/parser.mbt`, `src/prover/prover.mbt` | `src/parser/parser_test.mbt`, `src/prover/prover_positive_corpus_test.mbt` |
| Surface connector basis expansion | `src/logic/prop_prelude.mbt`, `src/logic/prop_foundation.mbt`, `src/logic/prop_tools.mbt` | `src/logic/prop_prelude_test.mbt`, `src/logic/prop_tools_test.mbt`, `src/parser/parser_test.mbt` |
| Proposition theorem replay/catalog seeds | `src/logic/prop_bool_theorems.mbt`, `src/logic/prop_refs.mbt`, `src/logic/prop_replay.mbt` | `src/logic/prop_bool_theorems_test.mbt`, `src/logic/prop_refs_test.mbt`, `src/logic/prop_replay_test.mbt` |
| Operational proof scripting + M1 subset replay | `src/tactics/proof_state.mbt`, `src/prover/prover.mbt` | `src/tactics/proof_state_test.mbt`, `src/tactics/tactics_test.mbt`, `src/prover/prover_test.mbt`, `src/prover/prover_positive_corpus_test.mbt`, `src/prover/prover_negative_corpus_test.mbt` |
| File-first `cmd` integration surface | `src/cmd/cmd.mbt` | `src/cmd/cmd_wbtest.mbt` |
| Quantifier-facing binder / raw-`forall` corpus + CLI contract | `src/prover/corpus.mbt`, `src/prover/prover_mapping_matrix_test.mbt`, `src/cmd/cmd_corpus_wbtest.mbt` | `src/cmd/cmd_corpus_wbtest.mbt`, `src/cmd/cmd_wbtest.mbt`, `src/prover/prover_mapping_matrix_test.mbt` |
| Formal Part I / Part II conformance pack | `formal_verification/QEDFV/Audit/PartI.lean`, `formal_verification/QEDFV/Engineering/Conformance.lean` | `lake build` |

Regression points that deserve particular attention:

- `src/kernel/kernel_audit_test.mbt` already covers high-risk scenarios such as def-head
  monotonicity, typedef witness validity, const-id drift, typed beta/trans guards, and conservative
  replay.
- `src/parser/parser_test.mbt` already covers the normalize/raw-offset contract and the fail-closed
  rejection of non-`bool` connectors.
- `src/parser/parser_test.mbt` currently also covers theorem-header binders, structured
  branch block parsing, and raw-span regressions.
- `src/parser/parser_test.mbt` and `src/prover/prover_positive_corpus_test.mbt`
  together currently pin down the contract for parser-owned goal lowering and the explicit
  upper-layer bridge to `tactics.Goal`.
- `src/prover/prover_test.mbt` currently pins down script scheduling, branch path attribution, and
  the step blame convention for structured branch blocks.
- `src/prover/prover_test.mbt` currently covers positive `Ok((KernelState, Thm))` cases for the
  supported M1 subset, as well as several direct-close / implication-backed theorem-name paths.
- `src/prover/prover_positive_corpus_test.mbt` / `src/prover/prover_negative_corpus_test.mbt`
  currently hold the canonical script corpus for the shipped subset, used to pin down capability
  coverage and the honest failure convention.
- `src/prover/prover_test.mbt`, `src/prover/prover_mapping_matrix_test.mbt`, and
  `src/cmd/cmd_corpus_wbtest.mbt` currently also cover the structured contract for unfinished-proof
  / hole reporting and the canonical unfinished corpus anchors.
- `src/prover/prover_mapping_matrix_test.mbt` and `src/cmd/cmd_corpus_wbtest.mbt`
  currently also cover the nested branch unfinished path and stable empty-marker rendering.
- `src/cmd/cmd_corpus_wbtest.mbt` and `src/cmd/cmd_wbtest.mbt` currently also pin down the
  success / failure / unfinished CLI contract for shipped quantifier-facing binder / raw-`forall`
  scripts, including goal, locals, branch path, and step blame.
- `src/prover/prover_mapping_matrix_test.mbt` currently binds the positive / negative /
  unfinished canonical case ids, the quantifier binder / raw-`forall` case ids, the capability tags,
  and the public example anchors in [User manual](manual.md) into a single set of regression constraints.
- `src/cmd/cmd_wbtest.mbt` currently covers success rendering, parse/io/usage failures,
  tactic failure context rendering, branch-path rendering, and the file-first argv
  workflow.

### Documentation example source contract

To keep the documentation from presenting planned capabilities as delivered ones, documentation
examples must currently follow these source constraints:

- `README.md` only publishes a summary of the current shipped subset and does not invent new
  example semantics on its own.
- Runnable theorem-script examples in [User manual](manual.md) must come from existing regression test
  coverage.
- Theorem-producing positive example scripts currently use
  `src/prover/prover_test.mbt` and `src/prover/prover_positive_corpus_test.mbt`
  as their primary anchors.
- Negative / honest failure examples for the shipped subset currently use
  `src/prover/prover_negative_corpus_test.mbt` as their primary anchor.
- Canonical unfinished-proof examples currently use
  `src/prover/prover_test.mbt`, `src/prover/prover_mapping_matrix_test.mbt`,
  and `src/cmd/cmd_corpus_wbtest.mbt` as their primary anchors; both root-level unfinished and
  nested branch unfinished samples must be kept in sync.
- Quantifier-facing binder / raw-`forall` examples currently also use
  `src/prover/corpus.mbt`, `src/prover/prover_mapping_matrix_test.mbt`, and
  `src/cmd/cmd_corpus_wbtest.mbt` as their primary anchors; public documentation may only cite
  these canonical case ids.
- The mapping from case ids to example anchors in public documentation currently uses
  `src/prover/prover_mapping_matrix_test.mbt` as its primary anchor.
- Tactic-level examples, local-over-name conflicts, and wrong-mode honest failures currently use
  `src/tactics/proof_state_test.mbt` as their primary anchor.
- If the documentation adds, modifies, or removes a public example, the corresponding regression
  test must be added, modified, or removed at the same time.

## Part II conformance obligations

Lean now states the Part II obligations of peripheral engineering explicitly as engineering
obligations. The core items are:

- `ruleFidelity`
- `boundaryFidelity`
- `scopeFidelity`
- `replayTraceFidelity`
- `gateFidelity`
- `certificateNonAuthority`
- `conservativeReplayFidelity`

For contributors, the more actionable checklist is the following set of rules.

### Contributor checklist

- `logic` may only provide checked wrappers, definition/unfold helpers, replay helpers, and
  organization of non-authoritative theorem references; it must not bypass the kernel to invent new
  rules.
- `parser` must preserve `local > const` and the normalize + raw-offset contract, and must share the
  same connector contract with `logic`.
- `elab` must freeze resolved identity; when later typing encounters const-id or schema drift, it
  must fail closed.
- `tactics` may hand out a theorem through `ps_qed` only when replay through `logic` constructs a
  `Thm` consistent with the sequent; otherwise it must fail closed.
- Final acceptance in `ps_qed` must currently use strict normalized sequent equality; the old
  boundary that admitted results based only on shape-aware compatibility must not be kept.
- `prover` returns `Ok` and a `Thm` only when replay succeeds; otherwise it keeps returning honest
  errors.
- `cmd` may only be a new non-authoritative integration layer and must not become a second proof
  kernel.
- Extension certificates may only be audit artifacts; they must not be treated as a substitute for
  theorem acceptance.

The goal of this checklist is to progressively compress the executable frontend into what the paper
calls a faithful realization, rather than adding a second logical system in peripheral engineering.

## Peripheral alignment

The engineering mainline of the current workspace is a deliberate consolidation:

- The parser has moved from "relying on a prelude constant of the same name existing in the state" to
  "basis-backed builder + resolve/lowering contract".
- Logic has advanced from "registering surface symbol names" to "defined constants + definition
  theorem + unfold/replay helpers + small theorem catalog + shared theorem inventory".
- Tactics/prover have moved from a purely operational prototype to "the supported subset replays to
  kernel `Thm`, with the support matrix and honest failures pinned down by the canonical corpus".

For peripheral engineering to keep conforming to the current core, it should continue to:

- extend replay builders on top of the shared theorem inventory and the canonical corpus;
- write new shipped capabilities back into the canonical corpus / mapping matrix /
  manual anchors, so the documentation does not lag behind the implementation;
- turn goal / hole / unfinished-proof diagnostics into a formal frontend contract, while continuing
  to state explicitly that they are not proof objects;
- keep the parser/lowering/replay boundaries explicit for the shipped quantifier-facing path of
  theorem-header binders, as well as for the raw `forall` theorem-goal sugar;
- have `cmd` keep reusing the structured failure contract of `prover` instead of interpreting error
  strings on its own;
- keep expanding frontend expressiveness on top of the current file-first workflow.

These tasks should reuse the existing tools:

- `logic_prop_def_*`
- `logic_prop_unfold_*`
- `logic_apply_fun_eq*`
- `logic_beta_normalize_eq`
- `logic_eq_mp_bool`
- `logic_eq_sym`
- `logic_prop_replay_*`

Do not create a separate ad-hoc proof semantics that holds only inside tactic/prover but cannot be
replayed to the kernel path.

## Remaining non-shipped surfaces

The capabilities that are still not shipped include:

- the theorem catalog is still small and not yet enough to support a large body of more natural
  scripts; however, the inventory, mode boundaries, and corpus of the current shipped subset are
  already fixed;
- the canonical corpus still needs its hardening regressions filled in to complete the `H5`
  integration gate;
- the theorem-script body already supports minimal `M4b` structured branch blocks, but richer proof
  blocks are still not implemented;
- holes / unfinished proofs have now entered the shipped theorem-script surface, but hole
  completion / metavariable authority is still not implemented;
- the theorem-header binder quantifier-facing surface is shipped; the raw
  `forall` / `∀` theorem-goal frontend is also supported as goal-only sugar;
- the parser-side utility surface has been consolidated into a non-script API; going forward,
  documentation and tests only need to be kept in sync;
- the Lean line is currently a paper/conformance pack, not a direct mechanized proof of the MoonBit
  source.

A more accurate assessment of the status is therefore:

- the Part I core and the main conformance conventions of Part II are in place;
- a theorem-producing frontend over the supported subset already exists;
- but a more complete faithful realization is still being consolidated.

## Verification gate

The currently recommended paper-alignment / engineering-conformance gate is:

```bash
moon build
moon test
cd formal_verification
lake build
```

When preparing to merge or freeze a release, also run:

```bash
moon info
moon fmt
moon test
cd formal_verification
lake build
```

Local check results on 2026-04-05:

- `moon test` passes
- `lake build` passes

When a change touches the trust boundary, scope, gates, the connector contract, proof scripting, or
documentation conventions, also check:

- [QED formal specification](../attachments/qed_formal_spec.typ)
- [User manual](manual.md)
- this document
