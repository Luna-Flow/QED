# Specification conformance

- Status: Typed HOL proof line active
- Audience: maintainers and reviewers
- Authority: [QED Typed HOL Core](../attachments/qed_formal_spec.typ)
- Scope: Lean mathematical core and the explicitly separated MoonBit boundary
- Last reviewed: 2026-10-12

The repository has one formal proof line: `formal_verification/QEDFV/HOL`. The
Lean library defines an intrinsically typed HOL calculus and proves its semantic
soundness. The MoonBit implementation remains a separate realization until a
checked refinement connects its terms, theorem objects, and kernel operations to
the Lean calculus.

## Evidence hierarchy

1. The Typst specification states the mathematical contract.
2. `formal_verification/QEDFV/HOL` defines and proves that contract in Lean.
3. MoonBit code and tests describe the current realization and its behavior.
4. This document records the boundary and verification commands; it does not
   add logical assumptions.

## Typed HOL evidence

| Area | Lean source | Result |
| --- | --- | --- |
| Types and non-empty carriers | `HOL/Types.lean` | proved |
| Intrinsic terms, renaming, substitution | `HOL/Terms.lean` | proved |
| Evaluation and beta | `HOL/Evaluation.lean` | proved |
| Type instantiation and choice coherence | `HOL/Instantiation.lean` | proved |
| Primitive rule validity, including `ADD_ASSUM` and witness `SPECIFY` | `HOL/Rules.lean` | proved |
| Derivation soundness | `HOL/Derivation.lean` | proved |
| Definition and specification contracts | `HOL/Definitions.lean`, `HOL/Specification.lean` | proved |
| Type-definition carrier laws | `HOL/TypeDefinitions.lean` | proved |
| Finite semantic conservativity | `HOL/Conservativity.lean` | proved |
| Concrete and signature-generic non-triviality | `HOL/Concrete.lean` | proved |
| Typed HOL core proof package | `HOL/Soundness.lean` | proved |

The public entry point is `QEDFV.HOL.typed_hol_core_proof_complete`. It covers
the typed core and fixed-signature semantic extension results. It does not
certify a growing-theory calculus. The default
`QEDFV` target imports `QEDFV.HOL.Soundness` only.

## Explicit limits

The Typed HOL theorem does not establish the infinity-axiom admission rule,
derivations for definitions and type-constructor extensions in a growing
theory, syntactic derivation erasure, or a MoonBit-to-Lean refinement. It also does not certify
the parser, elaborator, tactics, theorem replay, mutable scope history, or
provenance behavior. Those are implementation work and must not be presented as
evidence for the Lean theorem.

## Implementation evidence

The following mappings and contributor rules remain implementation evidence,
not a checked refinement theorem. Existing tests do not cover every trust-boundary
case: [issue #15](https://github.com/Luna-Flow/QED/issues/15) reports that
sibling `KernelState` histories can accept each other's theorems and derive
`T = F`. Its repair is deferred with the MoonBit work.

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
- Theorem scripts quoted on the package pages (`api/`, `design/`, `tutorial/`) reuse scripts from the
  anchors above; they do not introduce new script semantics.
- MoonBit API examples on the package pages are complete programs that call the public functions of the
  current code and record their results with `assert_eq`, `assert_true` or `inspect` snapshots. Every such
  block is compiled and run against the current code before the page changes; a block that is not meant to
  run is fenced `moonbit nocheck`.
- If the documentation adds, modifies, or removes a public example, the corresponding regression
  test must be added, modified, or removed at the same time.


## Contributor checklist

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

## Verification

Run the checks serially from the repository root:

```text
cd formal_verification
lake build
lake env lean --stdin <<'LEAN'
import QEDFV
#print axioms QEDFV.HOL.typed_hol_core_proof_complete
LEAN
cd ..
```

The public package reports only the Lean/Mathlib foundations `propext`,
`Classical.choice`, and `Quot.sound` under `#print axioms`. The exact audited
output and its role are recorded in `formal_verification/axioms.txt`. Typst
compilation is:

```text
typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-typed-hol-spec.pdf
```

MoonBit tests remain useful evidence for the realization, but they do not enlarge
the Typed HOL proof boundary.
