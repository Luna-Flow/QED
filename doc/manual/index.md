# QED

QED (Quite Easy Deduction) is a theorem prover for higher-order logic written in MoonBit. It follows the LCF approach: a small trusted kernel implements the primitive inference rules of HOL and is the only code that can create theorems, and everything else, from the parser to the command-line tool, builds on it without being trusted. Proofs are written as short theorem scripts with goal-directed steps; a script either yields a kernel theorem, fails with a structured diagnostic, or reports an unfinished proof. A formal specification defines the kernel, and a Lean 4 pack in `formal_verification/` checks the specification's conformance claims.

The shipped proof language covers propositional logic with equality, theorem-header binders and goal-level `forall`; the [user manual](manual.md) has the exact support matrix.

## Formal specification

The formal specification is the only normative source for the kernel.

[QED formal specification](../attachments/qed_formal_spec.typ)

## Packages

The packages are layered: each depends only on packages to its left, `kernel → logic/elab → parser → tactics → prover → cmd`, and only `kernel` is trusted.

| Package | Role | Pages |
| --- | --- | --- |
| `kernel` | Trusted kernel: types, terms, the abstract theorem type, primitive rules, scoped signature, extension gates | [API](api/kernel.md) · [design](design/kernel.md) · [tutorial](tutorial/kernel.md) |
| `logic` | Propositional connectives as definitions, derived rules, replay helpers, theorem catalog | [API](api/logic.md) · [design](design/logic.md) · [tutorial](tutorial/logic.md) |
| `elab` | Name resolution with frozen constant identities, core typing, lowering to kernel terms | [API](api/elab.md) · [design](design/elab.md) · [tutorial](tutorial/elab.md) |
| `parser` | Text frontend: normalisation, terms, goals, theorem scripts, source positions | [API](api/parser.md) · [design](design/parser.md) · [tutorial](tutorial/parser.md) |
| `tactics` | Backward proof states and steps, replayed forward to kernel theorems | [API](api/tactics.md) · [design](design/tactics.md) · [tutorial](tutorial/tactics.md) |
| `prover` | Theorem-script driver with structured results, and the regression corpus | [API](api/prover.md) · [design](design/prover.md) · [tutorial](tutorial/prover.md) |
| `cmd` | The command-line tool `qed-cmd` (executable package) | [API](api/cmd.md) · [design](design/cmd.md) · [tutorial](tutorial/cmd.md) |
| `research_rewrite` | Research-only rewriting prototype, not shipped | [API](api/research_rewrite.md) · [design](design/research_rewrite.md) · [tutorial](tutorial/research_rewrite.md) |

Blackbox test files (`*_test.mbt`) and the alias files `alias.mbt` and `alias_test.mbt` belong to their packages; [code governance](code_governance.md) defines their rules. The theorem files in `examples/` and `prelude/` are inputs for the command-line tool, not packages.

## Where to start

**New to proof assistants.** Read "For readers new to HOL" and the quick start in the [user manual](manual.md), then run the examples with the [cmd tutorial](tutorial/cmd.md). The [syntax guide](syntax.md) answers "how do I write this step".

**Using QED from MoonBit.** Start with the [prover tutorial](tutorial/prover.md) to run scripts and read results. Go down to the [tactics tutorial](tutorial/tactics.md) to drive proofs step by step, and to the [logic](tutorial/logic.md) and [kernel](tutorial/kernel.md) tutorials to build theorems forwards.

**Checking why it is sound.** Read the [kernel design](design/kernel.md), which derives the rules and explains why soundness reduces to the kernel, then the [logic](design/logic.md) and [tactics](design/tactics.md) designs, which show that the upper layers add no authority. The formal specification above is normative.

**Contributing.** Read [code governance](code_governance.md) and [documentation governance](governance.md) first, then [specification conformance](conformance.md) for the code/test mapping and the rules for examples. The [workspace audit](current_workspace_audit.md) lists open risks; the [specification changelog](qed_formal_spec_changelog.md) records revisions of the specification.

## Guides

- [User manual](manual.md): the user guide and implementation contract, with the support matrix and the stable examples.
- [Syntax guide](syntax.md): the theorem-script syntax.
- [Specification conformance](conformance.md): how code and tests align with the specification, and what contributors must do.
- [Documentation governance](governance.md) and [Code governance](code_governance.md): repository rules for documents, package layering and alias entry points.
- [Formal specification changelog](qed_formal_spec_changelog.md): revisions of the specification.
- [Workspace audit (2026-04-18)](current_workspace_audit.md): a point-in-time record of risks and gaps.

## Install and build

QED requires the MoonBit toolchain with `moonc` 0.10 or later, and depends on `moonbitlang/x` for file access in the command-line tool. To use the library from another module:

```bash
moon add Luna-Flow/QED@0.1.0
```

To work in the repository:

```bash
moon check --target all
moon test
moon run src/cmd examples/truth_file.qed
```

The Lean formalisation builds separately with `lake build` in `formal_verification/`.
