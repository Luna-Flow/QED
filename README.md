# QED (Quite Easy Deduction)

QED is a theorem prover for higher-order logic written in MoonBit, built kernel-first in the LCF tradition. A small trusted kernel implements HOL's primitive inference rules and is the only code that can create theorems; the parser, tactics, script driver and command-line tool build on it without being trusted, and every unsupported path fails closed instead of faking success. The normative mathematical core is specified in `doc/attachments/qed_formal_spec.typ` and formalized in Lean 4 as the intrinsically typed HOL development under `formal_verification/QEDFV/HOL`. The Lean proof does not yet establish a refinement from the MoonBit implementation.

## Current state

- `kernel`: checked primitive rules, scoped signature state and the `DefOK` / `TypeDefOK` / `SpecOK` extension gates.
- `logic`, `elab`, `parser`, `tactics`, `prover`: theorem scripts for propositional logic with equality, with theorem-header binders, goal-level `forall`, sequential and structured branch blocks, and `hole` for unfinished proofs.
- `cmd`: a file-first command-line tool with structured `error[...]` and `warning[unfinished]` reports.

The [user manual](doc/manual/manual.md) has the exact support matrix.
The [compliance review](doc/manual/conformance.md) records implementation
mapping, proof obligations, and separate Lean, MoonBit, refinement, and test
evidence.
The [formal branch contract](formal_verification/branch_contract.md) fixes the
promotion order from HOL theory through declaration growth to MoonBit
refinement and independent checking.
The dated [initial verification audit](research/qed-verification/2026-10-14-initial-audit.md)
records the evidence baseline and remaining research work; it is not a shipped
implementation contract.

## Install

The library requires MoonBit `moonc` 0.10 or later:

```bash
moon add Luna-Flow/QED@0.1.0
```

## Example

From the repository root, check the example file `examples/and_comm.qed`:

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
```

```bash
moon run src/cmd examples/and_comm.qed
```

```text
ok and_comm
```

The same script runs from MoonBit through the `prover` package:

```moonbit
let src = "theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by intro h; split { exact and_elim_r } { exact and_elim_l }"
match @prover.prove_theorem_script(@kernel.empty_kernel_state(), src, @prover.default_prover_options()) {
  Ok((_, thm)) => println(@kernel.thm_to_string(thm))
  Err(_) => println("not proved")
}
```

## Packages

| Package | Role |
| --- | --- |
| `src/kernel` | Trusted kernel: types, terms, abstract theorems, primitive rules, signature, extension gates |
| `src/logic` | Propositional connectives as definitions, derived rules, theorem catalog |
| `src/elab` | Name resolution with frozen constant identities |
| `src/parser` | Text frontend for terms, goals and theorem scripts |
| `src/tactics` | Backward proof states replayed to kernel theorems |
| `src/prover` | Theorem-script driver and regression corpus |
| `src/cmd` | Command-line tool `qed-cmd` |
| `src/research_rewrite` | Research-only rewriting prototype, not shipped |

## Build and verify

```bash
moon check --target all
moon test
moon info && moon fmt
```

The Typed HOL formalization builds with `lake build` in `formal_verification/`.

## Documentation

- Online: <https://lunaflow.cn/en/QED/>
- Source: [`doc/manual/index.md`](doc/manual/index.md), with the package pages (API, design, tutorial), the [user manual](doc/manual/manual.md), the [syntax guide](doc/manual/syntax.md), the [formal description](doc/manual/formal.md), and the [compliance review](doc/manual/conformance.md).
- Contributor obligations and evidence limits are maintained in the [compliance review](doc/manual/conformance.md). Research notes are in `research/` and are not part of the shipped contract.

## Contributing

Keep `kernel` the only theorem-construction boundary, respect the package layering, and update code, tests and documentation together; the [compliance review](doc/manual/conformance.md) lists the obligations. Commit messages follow Conventional Commits.

## License

Apache-2.0, see [`LICENSE`](LICENSE).
