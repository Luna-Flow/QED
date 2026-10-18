# Changelog

All notable changes to QED are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## Unreleased

### Changed

- Lean (`formal_verification`): **breaking change to the core syntax.** A constant occurrence `Term.const c τ h` now stores its instance *type* `τ` with a proof `h : (S c).IsInst τ`, instead of a total type substitution. Two occurrences at the same type are now the same term, which removes the "instance junk" (distinct terms differing only off the schema's support) that blocked the typedef erasure from older steps. Evaluation recovers the instance by `Ty.constSub`; the locality of the constant interpretation is now an explicit hypothesis of `valid_definition_equation`, `SpecificationGate.valid_constant` and `SpecificationExtension.valid_gate` (all callers have it from `Model.IsLocal`). The canonical-substitution machinery of the erasure (`canonSub`, `SigClean`, the `pred_clean` field) is deleted; `ConstRepl` is now `∀ c τ, (S c).IsInst τ → Term S [] τ`, and `Term.instType_congr` shows instantiation of a closed term depends only on its annotation variables. `eval_congr` takes the interpretation hypothesis per instance type.

### Added

- Lean (`formal_verification`): syntactic conservativity of a type definition without type parameters over the empty history (`TypeDefGate.typedef_conservative`, `TdMain.lean`, [#50](https://github.com/Luna-Flow/QED/issues/50)): a sequent in the old language that is derivable after the type definition is derivable before it, given a derivable witness of the predicate. The proof normalises instead of relativising: the retraction `norm` of the representation type onto the predicate, a translation of terms that sends the defined type to its representation type, keeps variables and normalises constants and binders, a translation of every rule of the calculus, and the three typedef laws as the properties of `norm`, proved at every type instance so that the instantiation rule is covered. Supporting files: `TdTypes`, `TdNorm`, `TdTerms`, `TdSubst`, `TdLaws`, `TdFL`, `TdRules`, `TdKfree`, `TdLaw`, `TdMain`. Parameterised type definitions and type definitions above other steps remain open.
- Lean (`formal_verification`): the rule `chooseHyp` (Hilbert choice from a witness derived under hypotheses, the form `P w ⟹ P (ε P)`), `DerivedRules.lean` (natural-deduction combinators: `impI`, `mp`, `cut`, `byCases`, `dne`, `sym`, `mkComb'`, `eqMp'`, `conjI`, ...), the type translation `Ty.tr` for closed representation types, and `TdNorm.lean`: the retraction `norm y = ε z. (P y ⟹ z = y) ∧ P z` of a typedef predicate with `⊢ P (norm t)`, `P t ⊢ norm t = t` and `⊢ norm (norm t) = norm t` from a derivable witness. Milestones W2 of [#50](https://github.com/Luna-Flow/QED/issues/50).
- Lean (`formal_verification`): `InstLaws.lean`, the instantiation laws needed for the typedef-erasure work ([#50](https://github.com/Luna-Flow/QED/issues/50), milestone W1): the substitution induced on type-instantiated contexts (`Sub.mapTypes`), commutation of type instantiation with term substitution (`Term.substitute_instType`), and composition of instantiations on arbitrary contexts (`Term.instType_instType_heq`, `typeSubstSequent_comp`). `Term.erase_inj_heq'` generalises the erasure injectivity lemma across contexts.
- Lean (`formal_verification`): rules for the primitive connectives and quantifiers in `Derivation` and `HistoryDerivation` (`truthIntro`, `falsityElim`, `conjIntro`, `conjElimLeft`, `conjElimRight`, `impIntro`, `impElim`, `allIntro`, `allElim`, `exIntro`, `exElim`, `classical`), each with a validity-preservation certificate (`ConnectiveRules.lean`) and a case in the definition and specification erasure theorems. The calculus previously could derive nothing about these constructors beyond equations; the kernel derives the same rules from the definitions in its propositional prelude. Non-vacuity examples in `ConnectiveExamples.lean`. This is milestone M1 of the typedef-erasure plan ([#50](https://github.com/Luna-Flow/QED/issues/50)); typedef erasure itself remains open.
- Tracking: syntactic erasure of type definitions (the relativisation translation) is split out of #17 into [#50](https://github.com/Luna-Flow/QED/issues/50). #17 is complete: type constructors, typedef semantics, history-indexed derivations, the obligation registry and gate, and definition and specification erasure are merged. The obligation `HOL-ERASE-001` stays partial until #50.
- Lean (`formal_verification`): syntactic erasure of a specification from a derivation (`HistoryDerivation.erase_specification`, `specification_conservative`, `SpecErasure.lean`, [#17](https://github.com/Luna-Flow/QED/issues/17)): the specified constant is replaced by the choice term of its instantiated predicate, and the step's theorem becomes the `chooseWitness` rule applied to the witness derivation. Together with definition erasure, only type-definition erasure remains open.
- Lean (`formal_verification`): syntactic erasure of a definition from a derivation (`HistoryDerivation.erase_definition`): a derivation at the history `definition D :: es` yields one at `es` of the sequent with the defined constant replaced by its instantiated definition, and a sequent not mentioning the constant is derivable unchanged (`definition_conservative`, [#17](https://github.com/Luna-Flow/QED/issues/17)). It rests on new term laws (`TermLaws.lean`: renaming and substitution fusion, closed terms, commutation of type instantiation with renaming, and the functor laws of type instantiation proved through an annotation-preserving erasure). `HistoryDerivation` gains the structural rule `weakenHyps` (hypotheses are a set). Erasure of specifications and type definitions remains open.
- Verification tooling: a machine-readable proof-obligation registry (`doc/manual/qed_obligations.json`) with a generator and validator (`tools/qed_obligations.py`) that writes the generated matrix into `doc/manual/conformance.md`, and a formal gate (`tools/qed_formal_gate.py`) that builds the Lean project, rejects `sorry`, `admit` and project axioms, and checks that the audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. Each obligation has separate Lean, MoonBit, refinement and test statuses with fixed definitions; no obligation is marked refined. The Lean workflow runs both and the gate's rejection paths are unit-tested (`tools/test_qed_formal_gate.py`).
- CI: a `MoonBit` workflow (`.github/workflows/moon.yml`) installs the latest MoonBit toolchain (no pinned version), runs `moon check --target all --deny-warn`, `moon fmt --check` and `moon test` on wasm, wasm-gc, js and native for pull requests and pushes that touch the MoonBit sources ([#13](https://github.com/Luna-Flow/QED/issues/13)).
- Lean (`formal_verification`): `HistoryDerivation` closes the fixed-signature
  history calculus under the supported core inference rules. Extension products
  can now be used as premises of `abs`, `trans`, `mkComb`, `eqMp`, `deduct`,
  instantiation, weakening, and witness-based choice; its soundness theorem is
  proved at the history's model pair. A checked example composes the derived
  `Abs (Rep a) = a` law into a closed function equation and records a local,
  admissible model that refutes the generic false sentence. Growing signatures,
  syntactic erasure, and MoonBit refinement remain outside this result.
- Lean (`formal_verification`): `DeclTable`, a finite declaration-table interface
  for the fixed-signature semantics, with the lemmas that a fresh allocation
  preserves old declarations and stays compatible with the total signature. It is
  an interface layer; it does not model name resolution or the executable kernel
  state.
- Lean (`formal_verification`): type definitions as history-indexed derivations.
  `ExtensionDerivation` is now indexed by histories of `ModelExtension` steps
  (definition, specification, type definition) and has one `typedef` constructor with a
  three-valued selector (`TypeDefLaw`) that derives `Abs (Rep a) = a`, `P (Rep a)` or
  `P r ⊢ Rep (Abs r) = r` from a mandatory hypothesis-free witness derivation `⊢ P w` at
  the preceding history; history freshness of `k`, `rep`, `abs` is a carried side
  condition. `weaken` across a type definition requires the sequent to mention neither the
  new constructor nor `rep`/`abs`. `extension_derivation_sound` returns validity at the
  history's model pair `interpretModels es M` for a local base model, with typed wrappers
  over the canonical models. Locality of the constant interpretation is carried through
  histories (`ModelExtension.interpret_isLocal`, `TypeDefGate.newConst_local`), which
  gives `valid_interpretModels_iff`, `typed_global_semantic_conservativity_models` and
  `extension_derivation_old_language_valid`. A worked example derives the three laws for
  the one-element subtype of `bool` and shows the extended model is non-trivial. Refs #17.

### Fixed

- Kernel: `ks_define_const` decides non-circularity by constant identity, not by name. A definition depends on itself only through an occurrence of its own name that does not denote a declared constant, which is still refused with `DefinitionIsCyclic`; an occurrence of an older constant of the same name (for example an outer constant that the new one shadows) is allowed, so `c := d` is accepted in an inner scope when an earlier definition of `d` mentions an outer, undefined `c`. This is the freshness condition of the Lean `DefinitionGate`. The name-based dependency table is removed; a second definition of one name is still refused. **Behavior change:** two definitions that used to be rejected as name-level cycles are now accepted. Closes [#9](https://github.com/Luna-Flow/QED/issues/9).
- Kernel: hypotheses are compared as propositions, ignoring constant identity stamps, when theorems are combined and when `DEDUCT_ANTISYM_RULE` removes a hypothesis. A constant built with `mk_const` (stamp `-1`) and the same constant built with `ks_mk_const` are one proposition and are no longer kept twice. Every checked rule has already shown its premises admissible in one state, where a constant name denotes one identity, so this is sound. Closes [#2](https://github.com/Luna-Flow/QED/issues/2).
- Tactics: `intro` on a quantified goal in the λ encoding stated the new subgoal about the binder name chosen by the kernel, which is fresh only for the conclusion, so a hypothesis with a free variable of the same name and type made the subgoal about that hypothesis (and `assumption` could close it, after which the replay failed in `ABS`). The subgoal is now stated about a variable that occurs neither in the hypotheses nor in the locals of the goal. Closes [#5](https://github.com/Luna-Flow/QED/issues/5).
- Logic: `logic_prop_unfold_and`, `logic_prop_unfold_imp` and `logic_prop_unfold_or` now return the basis form of the connective. `logic_beta_normalize_eq` contracts redexes along the application spine of the right-hand side, not only a redex at the very head, so `((λp q. b) a) c` is reduced; the two-argument unfolding used to stop at `(λp q. b) a c`. Closes [#11](https://github.com/Luna-Flow/QED/issues/11).
- Logic: `prop_mk_and` (and through it `prop_mk_imp`, `prop_mk_not` and `prop_mk_or`) built the conjunction with a binder named `_p_and` that was not renamed when an argument had a free variable of that name, so the variable was captured. The binder now gets a name that is not free in the arguments. Closes [#4](https://github.com/Luna-Flow/QED/issues/4).
- Parser: a `forall` after an infix operator, after `¬` or as an argument of an application in goal syntax is now refused by the raw parser at the offset of that `forall`; it used to be accepted and then refused during lowering with an error at offset 0. Closes [#6](https://github.com/Luna-Flow/QED/issues/6).
- Kernel boundary: theorem creation and lifting, the signature and extension-certificate accessors, and constants read from the signature now snapshot caller-owned type arrays, so mutating an array after admission cannot change admitted theorem data or kernel state. Terms and types built by the caller are not copied by `mk_*` and `dest_*`, so building and walking a term stays linear; the regression file `kernel_immutability_test.mbt` covers both, including a deep-term test.
- `thm_bind_const_ids` rejects rebinding of a theorem that has acquired declaration lineage and still contains an unstamped occurrence of a constant other than `=` and `@` (error `InvalidInstantiation`); this closes the descendant-shadowing admission path and is covered by a deterministic kernel regression.

### Changed

- Kernel: the extension-certificate table no longer computes its next index with the persistent map's `length`, which is linear in the map size and made building a theory quadratic. With the stored count, building 5000 definitions takes 33 ms (246 ms before this fix, [#37](https://github.com/Luna-Flow/QED/issues/37)), about 7 µs per definition at 2000 and at 5000; an `INST` call stays flat at about 2 µs. A regression test covers certificate order and count.
- Kernel: the global signature is a persistent structure (an immutable hash map from name to its stack of visible bindings, a shared list of scopes, and the next constant id), and the definition table, definition theorems and extension certificates are persistent maps. Name lookup, constant addition, scope push and pop, and `ks_define_const` no longer copy tables that grow with the number of declarations; a state version is shared structurally with its successors. On a native release build `ks_mk_const` after 2000 declarations drops from 7.2 µs to 0.1 µs and building 2000 definitions from 64 ms to 24 ms ([#37](https://github.com/Luna-Flow/QED/issues/37)). `GlobalSig` is now an opaque value; use `sig_scopes` to inspect scopes.
- API: `prove_theorem_script_with_diagnostics` is deprecated. It had the same signature and body as `prove_theorem_script`, and both return the full `ProverScriptError`; it now forwards to `prove_theorem_script` and will be removed in a later release. Closes [#12](https://github.com/Luna-Flow/QED/issues/12).
- Kernel: the declaration lineage is now a persistent, hash-consed chain with skew-binary jump pointers instead of an array that was copied on every event and every theorem and compared element by element. Appending an event and recording the lineage in a theorem are O(1); the prefix check that admits a theorem is O(log n). Lineage equality is unchanged (the same events from the same parent). Part of [#22](https://github.com/Luna-Flow/QED/issues/22); the remaining linear terms in the benchmark come from signature lookup and the definition tables, not from the lineage.
- Lean (`formal_verification`): `DefinitionGate.typeVarsClosed` and
  `SpecificationGate.typeVarsClosed` are now stated for `Term.annotVars` (the kernel's
  `term_tyvars` counts binder domains) instead of `Term.typeVars`, so that definition and
  specification steps preserve locality. `ExtensionDerivation` and
  `extension_derivation_sound` take histories of `ModelExtension` instead of
  `Extension κ S` (`Extension` and `interpretSequence` remain for the type-definition-free
  statement). Refs #17.

- Lean (`formal_verification`): semantics of a type-definition step. `TypeDefGate`
  models the checks of `ks_register_type_definition` (closed predicate over the
  declared parameters, new constructor, Rep and Abs constants); `TypeDefGate.interpret`
  builds the new model from an old one, with an admissible constructor interpretation;
  the three laws `Abs (Rep a) = a`, `P (Rep a)` and `P r ⊢ Rep (Abs r) = r` are proved
  valid in the new model (the second under the witness hypothesis), and validity of
  sequents that do not mention the new constructor or constants is preserved. The
  laws are available through the fixed-signature `ExtensionDerivation` and the
  compositional `HistoryDerivation` calculus. Refs #17.

- Upgrade the QED dependency on `moonbitlang/x` to `0.5.5` and verify it with
  MoonBit `0.10.15`. This registry-index repair is unrelated to the #15 theorem
  lineage fix; the old `0.4.41` entry no longer resolves from the current index.
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

- Specification and API documentation: the infinity registration (`ks_register_ind_infinity_axiom`) is documented as an audit marker, not a gate on the infinity sentence: it records a hypothesis-free admissible theorem that mentions `ind` and does not check that it states that `ind` is infinite, because the kernel has no infinity axiom (the mathematical statement is the Lean rule `Derivation.indInfinity`). The `SpecOK` witness is documented in the instance form `⊢ P[w]` for a closed `w`, which is what the specification already states and the gate checks. The obligation `HOL-INFINITY-001` is restated accordingly. Closes [#7](https://github.com/Luna-Flow/QED/issues/7) and [#8](https://github.com/Luna-Flow/QED/issues/8).
- Documentation: the three notes under `research/rewrite-simplify/` linked to absolute paths on a developer machine; the links are now repository-relative, and references to the planning note `PLAN.md`, which is not part of the repository, are plain text. Closes [#1](https://github.com/Luna-Flow/QED/issues/1).
- Specification layout: the Typst specification now follows a standards-document style (shared annotated-block system, numbered definitions and theorems, proofs with end marks, table of contents, running header, booktabs tables); display formulas that rendered as source text are real equations. No mathematical content changed.
- Documentation: merge the overlapping audit and status material into a dated research report (`research/qed-verification/2026-10-14-initial-audit.md`), a short workspace snapshot, the formal branch contract and the Typed HOL proof plan; delete the separate audit-matrices page (the generated obligation matrix replaces it); rewrite the implementation-conformance and governance pages with explicit claims, exclusions, reproduction commands and failure boundaries.
- Rewrite the manual overview and add API, design and tutorial pages for every package (`kernel`, `logic`, `elab`, `parser`, `tactics`, `prover`, `cmd`, `research_rewrite`), with examples that compile against the current code.
- Translate the manual into Chinese (`zh_CN`) and Japanese (`ja_JP`).
- Rewrite `README.md` in English and add this changelog.
- Update the documentation and code governance guides for the package pages, and the check results in the user manual and the conformance guide.
- Review the reasoning of the design and API pages against the code: correct the `TypeDefOK`, `SpecOK` and infinity-anchor arguments in the kernel design, describe the derivations of conjunction, implication and disjunction rules as the `logic` code performs them, describe the quantified `intro` replay, and replace imprecise complexity and completeness claims.
- Document behaviour found during the review: hypotheses are compared with constant identity stamps, the kernel rejects lineage-bearing theorems with raw shadowable constants during rebinding, definition checks are name-based, `prop_mk_and` captures a free variable named `_p_and`, and lowering errors for a nested `forall` carry offset 0.
- Restructure the manual overview and give every API page Purpose and Importing sections and every tutorial a task table, following the Luna-Flow documentation standard.
