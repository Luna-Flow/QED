# Documentation governance

- Status: active
- Audience: contributors, maintainers
- Authority: repository documentation policy; subordinate to [QED formal specification](../attachments/qed_formal_spec.typ)
- Scope: document hierarchy, naming, metadata, and cross-reference rules
- Last reviewed: 2026-04-16

This document defines the documentation governance rules for the QED repository. Its goal is not to add a
new specification layer but to strictly layer the existing documents by authority, purpose, and audience, so
that the same topic is not narrated repeatedly in several entry points and allowed to drift over time.

## Document layers

QED currently uses the following document layers:

1. Specification layer
   [QED formal specification](../attachments/qed_formal_spec.typ) is the only normative source; [`doc/attachments/qed_formal_spec.typ`](../attachments/qed_formal_spec.typ) is its source file.
2. Implementation layer
   The current code and regression tests determine the real shipped state.
3. Implementation documentation layer
   [User manual](manual.md), [Specification conformance](conformance.md), and [Workspace audit (2026-04-18)](current_workspace_audit.md) describe the current
   implementation contract, engineering conformance, and point-in-time audits.
4. Summary and navigation layer
   `README.md` and `application.typ` only provide summaries and entry-point navigation; they must not rank
   above the implementation layer or the implementation documentation layer.
5. Research layer
   `research/` only holds unshipped design research, promotion gates, go/no-go conclusions, and prototype
   evaluations. Research documents are not a product contract.

If code and documentation conflict, first establish the real state from code + tests, then write it back
into the implementation documentation.
If the implementation conflicts with the paper specification, the paper specification still prevails.

## Canonical entry points

Every category of information must have a single primary entry point:

- Current implementation contract: [User manual](manual.md)
- Quick reference for the current user input syntax: [Syntax guide](syntax.md)
- Engineering conformance and code/test mapping: [Specification conformance](conformance.md)
- Point-in-time risks and gaps: [Workspace audit (2026-04-18)](current_workspace_audit.md)
- Repository summary and quick entry point: `README.md`
- Research directory entry point: `research/README.md`

Other documents may only supplement these; they must not duplicate the "current state" in parallel.

Code organization and alias entry-point governance are defined in one place, [Code governance](code_governance.md); it
does not rank above the current code and implementation documentation, and only fixes engineering boundaries
and maintenance obligations.

## Metadata contract

Apart from the top-level `README.md` and the specification text itself, every maintenance-facing document
should include in its header:

- `Status`
- `Audience`
- `Authority`
- `Scope`
- `Last reviewed`

Status labels use the following vocabulary:

- `active`
- `point-in-time audit`
- `research-only`
- `superseded`
- `archival reference`

## Naming rules

- Implementation documents use responsibility-oriented names, such as `manual.md`, `conformance.md`, and `current_workspace_audit.md`.
- Research documents use a topic directory plus stage file names, all in lowercase kebab-case.
- New research topics go under `research/<topic>/`, for example `research/rewrite-simplify/`.
- Do not add temporary names such as `v2`, `new`, `tmp`, or `final`; when a replacement is needed, complete the migration directly and delete the old entry point.

## Content rules

- `README.md` may only contain:
  - a project introduction
  - a high-level summary of the current shipped subset
  - build commands
  - a documentation map
- `README.md` should not carry:
  - the full support matrix
  - long capability lists
  - audit details
  - details of future plans
- [User manual](manual.md) describes the current implementation boundary, module responsibilities, support matrix, and stable examples.
- [Syntax guide](syntax.md) only describes the current shipped theorem-script input syntax and known limitations; it does not serve as the implementation contract.
- [Specification conformance](conformance.md) describes specification alignment, code/test mapping, contributor checklists, and constraints on documentation examples.
- [Workspace audit (2026-04-18)](current_workspace_audit.md) only records risks, gaps, and follow-ups that still hold at a given point in time, and does not repeat the stable facts of manual/conformance over the long term.
- `research/` documents must explicitly declare `research-only`, `not shipped`, and `non-authoritative`.

## Example and reference rules

- Every publicly claimed capability must be traceable to the current code and regression tests.
- Public runnable examples must be anchored to existing tests; documentation must not invent untested scripts.
- `README.md` only summarizes capabilities and does not invent example semantics on its own.
- Research documents may refer to the shipped state, but should link to the implementation documentation instead of writing a separate long-lived status description.

## Current document map

- `README.md`
  Repository summary and navigation entry point.
- [User manual](manual.md)
  Current implementation contract.
- [Syntax guide](syntax.md)
  Quick reference for the current shipped theorem-script input syntax.
- [Specification conformance](conformance.md)
  Code/test mapping and engineering conformance.
- [Code governance](code_governance.md)
  Package layering, alias entry points, and code maintenance obligations.
- [Workspace audit (2026-04-18)](current_workspace_audit.md)
  Point-in-time audit of the current workspace.
- [Formal specification changelog](qed_formal_spec_changelog.md)
  Specification changelog; auxiliary material for specification maintenance.
- `research/README.md`
  Research directory entry point and boundary statement.

## Maintenance rule

When a change affects the implementation, the public capability claims, and research judgments at the same
time, maintain the documents in the following order:

1. Code and tests
2. [User manual](manual.md)
3. [Specification conformance](conformance.md)
4. `README.md`
5. [Workspace audit (2026-04-18)](current_workspace_audit.md)
6. Related `research/` documents
