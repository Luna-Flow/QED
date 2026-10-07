# QED

QED (Quite Easy Deduction) is a theorem prover written in MoonBit with a kernel-first architecture. The MoonBit implementation provides an executable, tested trusted kernel and a controlled frontend. A Lean 4 formalization in `formal_verification/` aligns the implementation with the paper specification for semantics, audit and conformance.

## Formal specification

The formal specification is the only normative source for the kernel.

[QED formal specification](../attachments/qed_formal_spec.typ)

## Packages

- **`kernel`** (`src/kernel`): the trusted kernel. See the [API reference](api/kernel.md), the [design notes](design/kernel.md) and the [tutorial](tutorial/kernel.md).
- **`parser`** (`src/parser`): the text frontend and its bridge to the kernel. See the [API reference](api/parser.md), the [design notes](design/parser.md) and the [tutorial](tutorial/parser.md).
- **`tactics`** (`src/tactics`): the proof-state execution engine. See the [API reference](api/tactics.md), the [design notes](design/tactics.md) and the [tutorial](tutorial/tactics.md).
- **`prover`** (`src/prover`): the theorem-script driver. See the [API reference](api/prover.md), the [design notes](design/prover.md) and the [tutorial](tutorial/prover.md).

## Guides

If you are new to the project, read the guides in this order:

1. [User manual](manual.md): the user guide and implementation contract, with background for readers new to HOL, simple proofs, command-line usage and the current support matrix.
2. [Syntax guide](syntax.md): a quick reference for the theorem-script input syntax.
3. [Specification conformance](conformance.md): how code and tests align with the specification, and what contributors must do.

The remaining guides serve maintainers:

- [Documentation governance](governance.md) and [Code governance](code_governance.md): repository rules for documents, package layering and alias entry points.
- [Formal specification changelog](qed_formal_spec_changelog.md): revisions of the specification.
- [Workspace audit (2026-04-18)](current_workspace_audit.md): a point-in-time record of the risks and gaps on the audited baseline.
