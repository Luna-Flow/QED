# Kernel Paper Traceability Matrix

Normative source: `doc/qed_formal_spec.pdf`

This file maps formal requirements to concrete implementation and regression tests.
The mapping is intentionally kernel-first and excludes non-kernel feature extensions.

## Trust Boundary

- `Thm` is opaque at package boundary (`type Thm` in `pkg.generated.mbti`).
- Raw primitive rules are internal-only in `src/kernel/thm.mbt`.
- External callers only use state-checked constructors and rules (`*_checked`).
- Type definition witness registration is fail-closed and state-admissibility checked.

## Chapter Mapping

| Spec area | Requirement | Implementation | Tests |
| --- | --- | --- | --- |
| Sec. 4-5 | Typed term/type core + boundary conversion | `src/kernel/types.mbt`, `src/kernel/terms.mbt` | `src/kernel/kernel_terms_test.mbt`, `src/kernel/kernel_types_test.mbt` |
| Sec. 6-7 | `(T,S)` model, scope discipline, monotone definition history | `src/kernel/sig.mbt` | `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Sec. 8 | `DefOK` and `TypeDefOK` side conditions | `src/kernel/sig.mbt` (`ks_define_const*`, `ks_register_type_definition`) | `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Sec. 9-11 | Primitive rule kernel + error taxonomy | `src/kernel/thm.mbt` | `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt` |
| Sec. 12-13 | Admissibility gate (`INST_TYPE`, theorem identity, schema-instance checks) | `src/kernel/thm.mbt`, `src/kernel/sig.mbt` | `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_audit_test.mbt` |

## Appendix Audit Mapping

| Appendix | Scenario family | Tests |
| --- | --- | --- |
| C | Def-head monotonicity, pop/redefine, cycle rejection | `audit c5`, `audit c6`, `audit c7` in `src/kernel/kernel_audit_test.mbt` |
| D | Type witness validity, schema-instance guard, witness const-id drift | `audit d1`, `audit d5`, `audit d6` in `src/kernel/kernel_audit_test.mbt` |
| E | Typed trans middle-term guard, beta binder agreement | `audit e2`, `audit e3` in `src/kernel/kernel_audit_test.mbt` |

## Primitive Rule Matrix

| Rule | Positive coverage | Failure coverage |
| --- | --- | --- |
| `REFL` | `thm is opaque and observable through API` | `rules reject malformed named binder typing at boundary` |
| `ASSUME` | `assume accepts only boolean propositions` | `assume accepts only boolean propositions` |
| `TRANS` | `trans composes equalities and checks alpha middle term` | `trans composes equalities and checks alpha middle term` |
| `MK_COMB` | `mk_comb_rule checks function typing constraints` | `mk_comb_rule checks function typing constraints`, `mk_comb_rule requires equality theorems on both inputs` |
| `ABS` | `abs_rule enforces binder and free-in-hyp side condition` | `abs_rule enforces binder and free-in-hyp side condition` |
| `BETA` | `beta_rule enforces redex shape and binder agreement` | `beta_rule enforces redex shape and binder agreement` |
| `EQ_MP` | `eq_mp derives rhs and checks lhs matching` | `eq_mp derives rhs and checks lhs matching`, `eq_mp validates equality shape and boolean side conditions` |
| `DEDUCT_ANTISYM_RULE` | `deduct_antisym_rule removes opposite assumptions` | indirectly guarded by `assume_checked` boolean theorem invariant |
| `INST_TYPE` | `inst_type validates substitution shape`, `inst_type enforces admissible type targets` | `inst_type validates substitution shape`, `inst_type enforces constant schema instances and theorem identity` |
| `INST` | `inst validates substitution map and types` | `inst validates substitution map and types`, `wb inst substitution rejects captured bound image` |

## Export Discipline (Current)

- Public theorem constructors/rules: checked interfaces only.
- Public signature mutation interfaces: error-typed `*_e` / `ks_*` interfaces.
- Legacy optional-return signature mutators are internal-only and no longer exported.

## Verification Gate

Use this gate for paper-alignment regressions:

```bash
moon build
moon test src/kernel
moon test
```
