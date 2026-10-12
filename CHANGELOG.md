# Changelog

All notable changes to QED are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## Unreleased

### Changed

- Upgrade the QED dependency on `moonbitlang/x` to `0.5.5` and verify it with
  MoonBit `0.10.15`.
- Dependency audit: `moon tree --package` finds no other registry dependency;
  `moonbitlang/core/env` is a toolchain package and the Luna Flow packages are
  local QED packages. No `luna-utils`, `luna-generic`, `arithmetic`, or
  `type_theory` release is required for this work.
- Record theorem origin lineage in the kernel and reject theorem and witness
  reuse across sibling declaration histories while preserving linear-history
  reuse; add regression coverage for the issue #15 reproduction and registration
  paths.
- Migrate to MoonBit 0.10: the module manifest is now `moon.mod` (replacing `moon.mod.json`), and `src/cmd` declares itself with `pkgtype(kind: "executable")` instead of `options("is-main": true)`.
- Reformat the sources with the MoonBit 0.10 `moon fmt`, which writes single-line struct literals with a trailing comma (`Goal::{ hyps, concl, }`). No behaviour or public API changed.
- Blackbox tests import their own package's names explicitly with `using @<package> { ... }` in each package's `alias_test.mbt`, as required by MoonBit's `test_unqualified_package` rule. `src/kernel` gains an `alias_test.mbt` for this purpose.
- Regenerate the `pkg.generated.mbti` interface files with the 0.10 toolchain (formatting only).

### Documentation

- Rewrite the manual overview and add API, design and tutorial pages for every package (`kernel`, `logic`, `elab`, `parser`, `tactics`, `prover`, `cmd`, `research_rewrite`), with examples that compile against the current code.
- Translate the manual into Chinese (`zh_CN`) and Japanese (`ja_JP`).
- Rewrite `README.md` in English and add this changelog.
- Update the documentation and code governance guides for the package pages, and the check results in the user manual and the conformance guide.
- Review the reasoning of the design and API pages against the code: correct the `TypeDefOK`, `SpecOK` and infinity-anchor arguments in the kernel design, describe the derivations of conjunction, implication and disjunction rules as the `logic` code performs them, describe the quantified `intro` replay, and replace imprecise complexity and completeness claims.
- Document behaviour found during the review: hypotheses are compared with constant identity stamps, `thm_bind_const_ids` rebinds unstamped constants after shadowing, the definition checks are name-based, `prop_mk_and` captures a free variable named `_p_and`, and lowering errors for a nested `forall` carry offset 0.
- Restructure the manual overview and give every API page Purpose and Importing sections and every tutorial a task table, following the Luna-Flow documentation standard.
