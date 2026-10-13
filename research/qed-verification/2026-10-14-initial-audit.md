# Initial QED verification audit (2026-10-14)

- Status: research-only
- Audience: maintainers, kernel reviewers, formalization contributors
- Authority: subordinate to [`qed_formal_spec.typ`](../../doc/attachments/qed_formal_spec.typ), current code and tests
- Scope: the initial specification, soundness and verification programme; this report is not a shipped contract
- Evidence revision: `origin/main` at `6bdcb24`, plus the uncommitted worktree changes recorded below
- Last reviewed: 2026-10-14

This report records the first QED verification baseline in the style used by the
Floating project: every claim has an evidence boundary, finite checks are named
with their command and target, and open work is kept separate from completed
results. It is a dated research record. The current implementation contract is
[`doc/manual/manual.md`](../../doc/manual/manual.md); the current implementation
mapping is [`doc/manual/conformance.md`](../../doc/manual/conformance.md); the
machine-readable status source is [`qed_obligations.json`](../../doc/manual/qed_obligations.json).

## Authority and evidence boundary

QED uses the following order when sources disagree or a claim is stronger than
its evidence:

1. The Typst document is the normative mathematical specification.
2. `formal_verification/QEDFV/HOL` proves properties of the Typed HOL calculus.
3. A future MoonBit-to-Lean correspondence may connect that calculus to the implementation.
4. MoonBit tests, audits and independent tools provide implementation evidence.
5. Manuals, examples and this report explain the other layers; they do not add axioms.

The present work has no source-level refinement theorem. A successful Lean build
therefore establishes Lean declarations, while a successful MoonBit test
establishes only the tested behavior. Neither result is reported here as
production-grade kernel soundness.

## Baseline claims

| Claim | Evidence | Scope of the claim |
| --- | --- | --- |
| Typed core rules are semantically sound | `QEDFV/HOL/Derivation.lean`, `Soundness.lean`, axiom audit | The fixed Typed HOL calculus and its explicit assumptions |
| History-indexed extension products compose with core rules | `HistoryDerivation.lean`, `HistoryDerivationExamples.lean`, `HistoryAuditExamples.lean` | Fixed total signature; validity at the history model pair |
| Fresh declaration allocation preserves the fixed signature entries | `DeclarationAllocation.lean`, `DeclarationAllocationExamples.lean` | The finite allocation slice; not a growing-signature transport theorem |
| Mutable aliases and sibling-history rebinding are rejected | `src/kernel/kernel_immutability_test.mbt`, kernel sources | Deterministic MoonBit regression cases; no Lean refinement claim |
| The generated obligation view is synchronized | `python3 tools/qed_obligations.py` | Registry paths and cited Lean declarations present in this checkout |

The Lean proof line reports only `propext`, `Classical.choice` and `Quot.sound`
as external foundations. See [`formal_verification/axioms.txt`](../../formal_verification/axioms.txt)
for the audited output.

## Completed repair and formal work

The baseline audit found a real representation-boundary defect: caller-owned
arrays could remain aliased into admitted theorem or state data. The kernel now
snapshots theorem data, signatures and extension certificates where they enter
or leave kernel-held state (theorem creation and lifting, signature and
certificate accessors, constants read from the signature). Types and terms that
the caller built are the caller's own values: the public constructors and
destructors do not copy them, so building and walking a term stays linear. A second repair rejects rebinding of a
lineage-bearing theorem that still contains raw shadowable constants. The
regression file covers both failures and the positive inherited-theorem path.

The formal line now contains three distinct layers. `HOL/Core` proves the
intrinsically typed rules. `HistoryModel` and `HistoryClosure` prove local
definition, specification and type-definition semantics and close them under
the supported rules. `GrowingSignature/Allocation` proves only the finite
allocation facts currently represented by `DeclTable`. The branch contract is
the authoritative promotion order; this report does not duplicate its table.

## Open obligations

The registry and generated matrix are the only current status list. The most
material open items are:

- growing-signature syntax, embeddings, model transport and committed-equation preservation;
- a checked MoonBit-to-Lean representation and constructor correspondence;
- an independent certificate checker that does not call MoonBit theorem constructors;
- exact executable correspondence for infinity admission, specification witnesses and name-based definition gates;
- a relativisation translation if syntactic type-definition erasure is required.

These are separate obligations. Semantic old-language validity, fixed-history
derivation soundness, growing-signature refinement and syntactic erasure must
not be collapsed into one green status.

## Reproducible evidence

The following commands were run from the repository root for this audit:

```text
python3 tools/qed_formal_gate.py
moon info
moon fmt
moon check --target all --deny-warn
moon test --target native --deny-warn
moon test --target wasm --deny-warn
moon test --target wasm-gc --deny-warn
moon test --target js --deny-warn
python3 tools/qed_obligations.py
python3 -m unittest discover -s tools -p 'test_*.py'
typst compile doc/attachments/qed_formal_spec.typ /tmp/qed-typed-hol-spec.pdf
lunadoc check . --compile
git diff --check
```

The MoonBit backend suites reported 369/369 tests on each target after the
kernel boundary fix landed ([#30](https://github.com/Luna-Flow/QED/pull/30)),
including its 10-case immutability regression file. The Lean history calculus
and the registry with its gate landed in
[#31](https://github.com/Luna-Flow/QED/pull/31) and
[#32](https://github.com/Luna-Flow/QED/pull/32). `lunadoc` reports 0 errors, 0
warnings and complete catalogs.

## Next promotion

The next formal increment is the growing-signature transport layer. It must
define embeddings and prove transport of types, contexts, terms, evaluation and
validity before a growing-history derivation is introduced. The next
implementation increment is a constructor-by-constructor representation
correspondence. Both tracks remain behind the `Refinement/MoonBit` promotion
gate in [`formal_verification/branch_contract.md`](../../formal_verification/branch_contract.md).
