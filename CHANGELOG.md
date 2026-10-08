# Changelog

All notable changes to QED are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## Unreleased

### Changed

- Migrate to MoonBit 0.10: the module manifest is now `moon.mod` (replacing `moon.mod.json`), and `src/cmd` declares itself with `pkgtype(kind: "executable")` instead of `options("is-main": true)`.
- Reformat the sources with the MoonBit 0.10 `moon fmt`, which writes single-line struct literals with a trailing comma (`Goal::{ hyps, concl, }`). No behaviour or public API changed.
- Blackbox tests import their own package's names explicitly with `using @<package> { ... }` in each package's `alias_test.mbt`, as required by MoonBit's `test_unqualified_package` rule. `src/kernel` gains an `alias_test.mbt` for this purpose.
- Regenerate the `pkg.generated.mbti` interface files with the 0.10 toolchain (formatting only).

### Documentation

- Rewrite the manual overview and add API, design and tutorial pages for every package (`kernel`, `logic`, `elab`, `parser`, `tactics`, `prover`, `cmd`, `research_rewrite`), with examples that compile against the current code.
- Translate the manual into Chinese (`zh_CN`) and Japanese (`ja_JP`).
- Rewrite `README.md` in English and add this changelog.
- Update the documentation and code governance guides for the package pages, and the check results in the user manual and the conformance guide.
