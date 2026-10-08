# QED

This manual documents `v0.1.0` of `Luna-Flow/QED`, as it stands on `main`.

## Overview

QED (Quite Easy Deduction) is a theorem prover for higher-order logic written in MoonBit. It follows the LCF approach: a small trusted kernel implements the primitive inference rules of HOL and is the only code that can create theorems, and everything else, from the parser to the command-line tool, builds on it without being trusted. Proofs are written as short theorem scripts with goal-directed steps; a script either yields a kernel theorem, fails with a structured diagnostic, or reports an unfinished proof. A formal specification defines the kernel, and a Lean 4 pack in `formal_verification/` checks the specification's conformance claims.

The shipped proof language covers propositional logic with equality, theorem-header binders and goal-level `forall`; the [user manual](manual.md) has the exact support matrix.

## Install

```bash
moon add Luna-Flow/QED@0.1.0
```

Then import the packages you need in your `moon.pkg`, for example `"Luna-Flow/QED/prover"` to run theorem scripts or `"Luna-Flow/QED/kernel"` to build theorems directly. QED needs the MoonBit toolchain 0.10 or later (`moonc` ≥ 0.10), and depends on `moonbitlang/x` for file access in the command-line tool.

To work in the repository:

```bash
moon check --target all
moon test
moon run src/cmd examples/truth_file.qed
```

## Formal specification

The formal specification is the only normative source for the kernel.

[QED formal specification](../attachments/qed_formal_spec.typ)

## Pages

The packages are layered: each depends only on packages to its left, `kernel → logic/elab → parser → tactics → prover → cmd`, and only `kernel` is trusted. `research_rewrite` sits outside this chain.

| Part | Tutorial | API | Design |
| --- | --- | --- | --- |
| `kernel`: types, terms, theorems, primitive rules, scoped signature, extension gates | [tutorial](tutorial/kernel.md) | [API](api/kernel.md) | [design](design/kernel.md) |
| `logic`: connectives as definitions, derived rules, replay helpers, theorem catalog | [tutorial](tutorial/logic.md) | [API](api/logic.md) | [design](design/logic.md) |
| `elab`: name resolution with frozen constant identities, core typing, lowering | [tutorial](tutorial/elab.md) | [API](api/elab.md) | [design](design/elab.md) |
| `parser`: normalisation, terms, goals, theorem scripts, source positions | [tutorial](tutorial/parser.md) | [API](api/parser.md) | [design](design/parser.md) |
| `tactics`: backward proof states, replayed forward to kernel theorems | [tutorial](tutorial/tactics.md) | [API](api/tactics.md) | [design](design/tactics.md) |
| `prover`: theorem-script driver, structured results, regression corpus | [tutorial](tutorial/prover.md) | [API](api/prover.md) | [design](design/prover.md) |
| `cmd`: the command-line tool `qed-cmd` (executable package) | [tutorial](tutorial/cmd.md) | [API](api/cmd.md) | [design](design/cmd.md) |
| `research_rewrite`: research-only rewriting prototype, not shipped | [tutorial](tutorial/research_rewrite.md) | [API](api/research_rewrite.md) | [design](design/research_rewrite.md) |

Repository guides:

| Guide | Contents |
| --- | --- |
| [User manual](manual.md) | The user guide and implementation contract, with the support matrix and the stable examples |
| [Syntax guide](syntax.md) | The theorem-script syntax |
| [Specification conformance](conformance.md) | How code and tests align with the specification, and what contributors must do |
| [Documentation governance](governance.md) and [code governance](code_governance.md) | Repository rules for documents, package layering and alias entry points |
| [Formal specification changelog](qed_formal_spec_changelog.md) | Revisions of the specification |
| [Workspace audit (2026-04-18)](current_workspace_audit.md) | A point-in-time record of risks and gaps |

Blackbox test files (`*_test.mbt`) and the alias files `alias.mbt` and `alias_test.mbt` belong to their packages; [code governance](code_governance.md) defines their rules. The theorem files in `examples/` and `prelude/` are inputs for the command-line tool, not packages.

## Exported items

### Trusted kernel

- Types and terms: `HolType`, `Term`, `DbTerm` and their constructors, destructors and substitutions
- Theorems: the abstract `Thm`, read with `thm_concl`, `thm_hyps` and `thm_is_admissible`
- Primitive rules: `refl_checked`, `assume_checked`, `trans_checked`, `mk_comb_rule_checked`, `abs_rule_checked`, `beta_rule_checked`, `eq_mp_checked`, `deduct_antisym_rule_checked`, `inst_type`, `inst_checked`, and the derived `add_assum_checked`
- State and gates: `KernelState`, scopes, `ks_define_const_thm` (`DefOK`), `ks_register_type_definition` (`TypeDefOK`), `ks_specify_const` (`SpecOK`), audit certificates

### Untrusted layers

- `logic`: `install_prop_prelude`, the connective builders `prop_mk_*` and recognisers `prop_dest_*`, the natural-deduction rules `logic_prop_*_thm`, the theorem catalog
- `elab`: `RTerm`, `elab_resolve_*`, `elab_check_core_type`, `elab_lower_to_term`
- `parser`: `parse_term`, `parse_goal`, `parse_theorem_script_raw` and their `_raw` and `_with_env` variants, `ParseError` with raw offsets
- `tactics`: `ProofState`, `ps_init`, `ps_apply`, `ps_qed`, the steps `step_intro`, `step_split`, `step_left`, `step_right`, `step_apply`, `step_exact`, `step_assumption`
- `prover`: `prove_theorem_script_detailed`, `prove_theorem_file_results_detailed`, `ProverRunResult`, the regression corpus

## Where to read next

- New to proof assistants: read "For readers new to HOL" and the quick start in the [user manual](manual.md), then run the examples with the [cmd tutorial](tutorial/cmd.md). The [syntax guide](syntax.md) answers "how do I write this step".
- Using QED from MoonBit: start with the [prover tutorial](tutorial/prover.md) to run scripts and read results. Go down to the [tactics tutorial](tutorial/tactics.md) to drive proofs step by step, and to the [logic](tutorial/logic.md) and [kernel](tutorial/kernel.md) tutorials to build theorems forwards. Keep the API pages at hand; each lists the failure cases of every function.
- Checking why it is sound: read the [kernel design](design/kernel.md), which derives the rules and explains why soundness reduces to the kernel, then the [logic](design/logic.md) and [tactics](design/tactics.md) designs, which show that the upper layers add no authority. The formal specification above is normative.
- Contributing: read [code governance](code_governance.md) and [documentation governance](governance.md) first, then [specification conformance](conformance.md) for the code/test mapping and the rules for examples. The [workspace audit](current_workspace_audit.md) lists open risks; the [specification changelog](qed_formal_spec_changelog.md) records revisions of the specification.

## Validation

Recommended release checks:

```bash
moon check --target all
moon test
```

The examples on the package pages compile against the current code; [specification conformance](conformance.md) describes how they are checked. The Lean formalisation builds separately with `lake build` in `formal_verification/`.
