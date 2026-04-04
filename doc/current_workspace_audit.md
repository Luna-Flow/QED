# Current Workspace Audit

_Date: 2026-04-04_

This report audits the **current dirty workspace** against the repository's stated source-of-truth order:

1. `doc/qed_formal_spec.pdf` Part I
2. Part II conformance obligations
3. current implementation docs (`README.md`, `doc/manual.md`, `doc/conformance.md`)
4. current code reality

Validation baseline used during this audit:

- `moon test` -> pass (`187/187`)
- `formal_verification/lake build` -> pass

These green gates show the workspace is internally runnable, but they do **not** by themselves establish Part I fidelity.

## Findings

### [P1] Type-language admissibility is not enforced at the theorem and sentence boundaries

**Why this violates the spec**

Part I's type grammar restricts object-language types to constructors in the current type signature (`tau ::= alpha | k(...)`, with `k in Sigma_t`; see `doc/qed_formal_spec.typ:300-336`). In the current MoonBit code, arbitrary `TyApp("ghost", ...)` terms can flow into kernel terms, theorem objects, and `SentenceInLanguage` checks without any state-level admissibility gate.

**Evidence**

- `type_of` is purely structural and accepts any `TyApp`, with no signature check: `src/kernel/terms.mbt:113-137`
- `ks_add_const` admits constants without calling `ks_type_is_admissible`: `src/kernel/sig.mbt:442-489`
- theorem admissibility never calls `ks_type_is_admissible` or an equivalent whole-term type-language check: `src/kernel/thm.mbt:706-732`
- `term_const_instances_ok` only checks constant schema/const-id shape and ignores variable/binder types and tycon membership: `src/kernel/sig.mbt:846-863`
- `ks_thm_is_sentence_in_language` delegates to `term_const_instances_ok`, so it also ignores ghost type constructors: `src/kernel/sig.mbt:978-1003`

**Minimal repro**

Static construction is enough:

```moonbit
let ghost = mk_tyapp("ghost", [])
let idg = mk_abs(mk_var("x", ghost), mk_var("x", ghost))
let th = refl_checked(empty_kernel_state(), idg)
```

`idg` is closed, `idg = idg` is boolean, and there are no ordinary constants to reject. Under the current checks, this shape is eligible to pass `thm_is_admissible` and can also satisfy `ks_thm_is_sentence_in_language`, even though `ghost` is not in the current type language.

**Impact**

- Part I `Sigma_t` discipline is not actually enforced by the exported kernel boundary.
- `SentenceInLanguage` / `ConservativeReplayOK` can produce false positives over out-of-language formulas.
- definition/specification/theorem audits are weaker than the docs claim.

**Suggested fix**

- Require `ks_type_is_admissible` at every trusted admission boundary that accepts externally supplied types or terms.
- Add a whole-term / whole-theorem admissibility check that walks all embedded types, including binders and variables.
- Make `ks_thm_is_sentence_in_language` check type-language membership, not just constant-schema membership.

### [P1] Connector head-name collisions can make the prover accept a theorem whose conclusion is not the parsed goal

**Why this violates the contract**

The docs say surface connectors are basis-backed logical encodings and are not supposed to become an extra logic authority in `tactics` or `prover` (`doc/manual.md:132-142`). In the current code, connector destructors first recognize `imp/and/or/not` **by constant head name**, and prelude installation silently accepts an existing same-typed constant under those names. That creates a path where tactic execution and final root-goal compatibility can treat an arbitrary user constant as a logical connective.

**Evidence**

- prelude installation treats a same-typed existing constant as success instead of requiring the trusted definition theorem: `src/logic/prop_prelude.mbt:107-170`
- connector destructors prefer head-name matching before semantic unfolding:
  - `prop_dest_imp`: `src/logic/prop_prelude.mbt:282-295`
  - `prop_dest_and`: `src/logic/prop_prelude.mbt:298-327`
  - `prop_dest_or`: `src/logic/prop_prelude.mbt:330-343`
  - `prop_dest_not`: `src/logic/prop_prelude.mbt:346-360`
- implication introduction synthesizes the **basis-backed** target via `prop_mk_imp`, not the original head-named term: `src/logic/prop_bool_theorems.mbt:431-489`
- final theorem/root-goal compatibility also uses `prop_dest_imp` recursively, so it can accept a head-name match even when the actual terms differ: `src/tactics/proof_state.mbt:283-359`
- current tests only cover happy-path roundtrips by head symbol and do not cover collision cases: `src/logic/prop_prelude_test.mbt:10-80`

**Minimal repro**

The risky shape is:

```moonbit
let st0 = ks_add_const(empty_kernel_state(), "imp", fun_ty(bool_ty(), fun_ty(bool_ty(), bool_ty())))
let st1 = install_prop_prelude(st0)
-- goal written with ordinary application syntax, not surface `->`
-- theorem bad : imp P P := by intro h; exact h
```

Operationally, `intro`/root matching can read `imp P P` as a logical implication because `prop_dest_imp` accepts the head name. The replay path, however, synthesizes the basis encoding produced by `prop_mk_imp`. That is a root-goal mismatch hidden by name-based compatibility.

**Impact**

- `prove_theorem_script` can return a trusted theorem that does not actually match the user's parsed goal term under collision scenarios.
- this is a correctness issue in the theorem-producing frontend, even if Part I primitive rules remain unchanged.

**Suggested fix**

- reserve or strongly protect prelude connector names once their logical role is in use
- make `install_prop_prelude` require the trusted definition theorem, not just same-type name occupancy
- make `prop_dest_*` prefer semantic unfolding / definition-theorem-backed recognition over raw head-name matching
- make `root_matches_thm` compare the actual target term after controlled unfolding, not connector-by-name compatibility

### [P2] Surface connector builders can panic on user-reachable non-bool inputs instead of failing closed

**Why this violates the contract**

The current docs repeatedly promise fail-closed behavior at the parser/elab/tactic/prover boundary. The connector builders currently use `panic()` as an internal assertion, but the parser calls them directly on user input.

**Evidence**

- `expect_prop_term` panics on any `mk_eq` failure: `src/logic/prop_prelude.mbt:40-44`
- `prop_and_term`, `prop_imp_term`, `prop_false_term` and derived builders rely on that panic path: `src/logic/prop_prelude.mbt:61-104`
- parser lowering for `¬`, `->`, `∧`, `∨` calls `prop_mk_*` directly from user syntax: `src/parser/parser.mbt:1356-1467`

**Minimal repro**

With local non-bool variables, a source term like:

```moonbit
let env = ParseEnv::{ locals: [("x", mk_tyvar("A")), ("y", mk_tyvar("A"))] }
parse_term_with_env(empty_kernel_state(), env, "x -> y")
```

should produce an honest `Logic(TypeMismatch)`-style error. Today the builder path can panic before the parser returns a structured bridge error.

**Impact**

- parser/prover fail-closed guarantees are weaker than documented
- malformed but ordinary user input can become a crash instead of a typed rejection

**Suggested fix**

- make `prop_mk_not/imp/and/or` validate bool operands explicitly and return `Result`
- remove `panic()` from user-reachable proposition builder paths
- add negative parser tests for non-bool connectors

### [P3] The Lean line is a paper/conformance model, not a direct machine-checked proof of the current MoonBit program

**Why this matters**

This is not a kernel bug by itself, but it is important for honest status reporting. `lake build` currently proves the paper model and abstract conformance obligations. It does **not** mechanically bind the current MoonBit source tree to the Lean `Realization`.

**Evidence**

- `formal_verification/QEDFV/Engineering/Conformance.lean` defines an abstract `Realization` record and proves properties about realizations satisfying the obligations: `formal_verification/QEDFV/Engineering/Conformance.lean:1-220`
- `formal_verification/QEDFV/Engineering/RuleMapping.lean` maps rule names to Lean declarations, not to concrete MoonBit symbols: `formal_verification/QEDFV/Engineering/RuleMapping.lean:1-18`
- `formal_verification/QEDFV/Spec/Traceability.lean` proves coverage over declared spec items, again inside the Lean model: `formal_verification/QEDFV/Spec/Traceability.lean:1-23`

**Impact**

- `lake build` should be read as “paper-first spec/conformance pack is closed”, not “the running MoonBit implementation is mechanically proved equivalent to Lean”
- README/docs should stay precise on this point to avoid overstating assurance

**Suggested fix**

- keep the current paper-first FV line
- tighten wording wherever `lake build` could be misread as direct implementation verification
- if stronger assurance is desired later, introduce an explicit MoonBit-to-Lean trace or extraction/bisimulation story as a new milestone

## Dead Code / Noise Disposition

### Confirm deletion

- `src/cmd/main.mbt` `run_cli_phase0`
  - reason: old demo path only; current roadmap already says it should be replaced by real file-based commands
- package-wide `*_phase0_ready()` probes
  - reason: current usage is test-only scaffolding and no longer carries product meaning

### Move to experimental or test helper status

- `src/tactics/engine.mbt` (`solve_by_assume`, `solve_by_refl`, `solve_by_trans`, `solve_by_hyp`)
  - reason: these helpers are still useful as smoke utilities, but they are not the current theorem-script product path and currently blur the boundary between old demo scaffolding and live prover behavior

### Keep, but document explicitly

- `parse_let`
- `parse_def_function`

These parser APIs are public and tested, so they should currently be treated as live surface area. However, they are absent from the current main product docs and are not wired into the theorem-script driver. If they remain public, they should be documented as parser-side utility/experimental facilities with an explicit status label.

## Missing Negative Tests

The current test suite is strong on happy paths and many kernel invariants, but the following high-risk regressions should be added explicitly:

1. unknown type constructor enters a closed theorem / `SentenceInLanguage` / `ConservativeReplayOK`
2. same-typed connector-name collision (`imp/and/or/not`) against the theorem-script path
3. non-bool connector parse returns a structured error instead of panicking
4. old demo helpers and main theorem-script path cannot disagree on what counts as a solved goal

## Overall Assessment

- **Kernel Part I fidelity is not yet fully closed** because type-language admissibility is under-enforced at trusted theorem/language boundaries.
- **Frontend theorem production is not fully self-consistent** under connector-name collision scenarios.
- **Most remaining issues are fixable without enlarging the TCB**: they are primarily missing guards, over-permissive connector recognition, and stale demo scaffolding.
- **The Lean line is valuable and green**, but it should continue to be described as a paper/conformance pack unless and until a direct implementation binding is added.
