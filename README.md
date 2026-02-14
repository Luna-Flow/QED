# QED (Quite Easy Deduction)

QED 是一个基于 MoonBit 的交互式定理证明器。当前开发以
`doc/qed_formal_spec.pdf` 为唯一规范源，核心目标是构建 LCF 风格的可信内核。

## 当前内核状态（paper-aligned）

- `Thm` 已改为抽象对象（opaque），包外无法直接构造定理值。
- primitive rules 统一使用显式失败语义（`Result[Thm, LogicError]`）。
- 新增 state-checked 规则入口（`*_checked`）并在 logic/tactics/cmd 路径默认走 checked API。
- 新增 state-bound 常量构造入口（`ks_mk_const` / `ks_mk_const_instance`），上层默认不直接伪造命名常量。
- 等式构造 `mk_eq` 强制同型输入，拒绝异型等式。
- 签名层包含 scope + theory 双层状态入口，并对 reserved symbol (`=`) 做硬约束。
- `DefHeads` 单调历史、typedef `Rep` 头历史、以及定义依赖图门禁已落地到状态 API。
- typedef 注册要求 witness 对当前状态可采纳（`thm_is_admissible`），并拒绝常量身份漂移后的 witness 复用。
- 旧的 optional-return `sig_*` 变更接口已内收，不再作为 kernel 公共入口导出。
- `SigError` 与 `LogicError` 已统一采用 MoonBit `suberror` 风格定义，错误分类可模式匹配且可扩展。
- `kernel_audit_test.mbt` 已覆盖 Appendix C/D/E 的关键审计场景（定义历史、typedef 见证、多态实例、typed de Bruijn 守卫）。
- `kernel_thm_wbtest.mbt` 额外覆盖 substitution capture 的白盒守卫（`VariableCaptured` 路径）。

## 论文映射（kernel）

- `Chapter 4-5`（types/terms 与边界转换）：`src/kernel/types.mbt`, `src/kernel/terms.mbt`, `src/kernel/kernel_terms_test.mbt`
- `Chapter 6-7`（state model, scope discipline, DefHeads）：`src/kernel/sig.mbt`, `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt`
- `Chapter 8`（DefOK / TypeDefOK）：`src/kernel/sig.mbt`, `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt`
- `Chapter 9-11`（10 primitive rules + error semantics）：`src/kernel/thm.mbt`, `src/kernel/kernel_thm_test.mbt`
- `Appendix C/D/E`（审计矩阵）：`src/kernel/kernel_audit_test.mbt`
- 详细 traceability 矩阵：`doc/kernel_paper_traceability.md`

## 项目结构

```text
src/
├── kernel/     # Trusted Kernel (LCF boundary)
├── logic/      # Logic layer (minimal placeholders)
├── tactics/    # Tactic layer (minimal placeholders)
└── cmd/        # CLI layer (minimal placeholders)
```

## 开发命令

```bash
moon build
moon test src/kernel
moon test
moon info
moon fmt
```

当前默认门禁：`moon info && moon fmt && moon test`（同时覆盖 kernel 与上层 smoke 适配）。

## 执行计划

详细分阶段计划见 `PLAN.md`。
