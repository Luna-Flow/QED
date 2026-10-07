# Code governance

- Status: active
- Audience: contributors, maintainers
- Authority: repository code-organization policy; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ), current code/tests, and [Documentation governance](governance.md)
- Scope: package layering, alias entrypoints, source responsibilities, and code-change documentation obligations
- Last reviewed: 2026-04-18

This document defines the code governance rules for the QED repository. It adds no new semantic
specification layer; it only fixes package boundaries, alias entry points, and documentation write-back
obligations, so that the code structure does not drift over time.

## Layering

The default dependency direction is fixed as:

`kernel -> logic/elab -> parser -> tactics -> prover -> cmd`

Governance requirements:

- `kernel` is the only theorem-construction boundary.
- `logic` may only provide checked helpers, definition/unfold, replay helpers, and theorem catalog organization; it must not add new primitive authority.
- `parser` is only responsible for textual syntax, normalization, resolution, and lowering; it must not depend directly on tactics execution objects.
- `tactics` is only responsible for goal-state transformation and replay orchestration; it must not write back into parser semantics.
- `prover` only orchestrates parser/tactics/kernel and produces structured diagnostics; it must not become a new logical authority.
- `cmd` stays the thinnest outer layer; it only consumes stable facades and adds no low-level knowledge.

If a change requires a reverse dependency, treat it as a design problem by default; prefer introducing a
neutral data structure or an explicit bridge over a direct cross-layer reference.

## Alias entry points

Each package has exactly two kinds of official alias entry points:

- `alias.mbt`
  Production source entry point.
- `alias_test.mbt`
  Blackbox test entry point.

The constraints are:

- `alias.mbt` only exposes the stable symbols that the package's production source actually needs.
- `alias_test.mbt` must first mirror the production exports of `alias.mbt`, then add test-only imports.
- `alias_test.mbt` is not a second public API; it must not follow an export philosophy different from the production entry point.
- The header comment of an alias file must state the scope of the entry point and its maintenance rules.
- An alias file must not be used as an unbounded re-export table for lower-layer symbols.
- When a blackbox test references symbols of its own package, `alias_test.mbt` must import them explicitly with `using @<package> {...}` (MoonBit's `test_unqualified_package` rule); tests must not rely on implicit imports.
- `kernel` depends on no other QED package, so it has no `alias.mbt`, only an `alias_test.mbt` that lists the package symbols its tests use.

## Source responsibilities

A single file or module should, as far as possible, carry only one primary responsibility:

- pure data objects and accessors
- pure lowering / normalization / rendering
- replay / orchestration
- corpus / mapping / fixtures

The following cases should be split first:

- orchestration logic and error rendering stay mixed in the same file over the long term
- parser-side lowering constructs tactics objects directly
- a façade-layer file gradually turns into a cross-layer catch-all entry point

The first governance patterns currently in place in this repository include:

- parser outputs a parser-owned `ParsedGoal`, which the upper layer explicitly bridges to `tactics.Goal`
- prover keeps its orchestration role, but continues to separate diagnostic rendering and corpus data from the main execution path

## Documentation obligations

When a code change affects any of the following, the documentation must be updated in step:

- public capability claims
- package responsibilities or layering boundaries
- alias entry-point semantics
- failure semantics or structured diagnostic fields

Default maintenance order:

1. Code and tests
2. [User manual](manual.md)
3. [Specification conformance](conformance.md)
4. `README.md`
5. [Workspace audit (2026-04-18)](current_workspace_audit.md) (only when the point-in-time conclusions change)

## Review checklist

On submission and review, check at least:

- whether new dependencies follow the established layering
- whether `alias.mbt` / `alias_test.mbt` are still the single official entry points
- whether the responsibilities of parser/tactics/prover are being coupled together again
- whether `.mbti` changes match the intended public boundary
- whether the documentation reflects the new shipped state in step
