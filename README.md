# QED (Quite Easy Deduction)

QED 是一个基于 MoonBit 的交互式定理证明器。当前开发以
`doc/qed_formal_spec.pdf` 为唯一规范源，核心目标是构建 LCF 风格的可信内核。

## 当前内核状态（paper-aligned）

- `Thm` 已改为抽象对象（opaque），包外无法直接构造定理值。
- primitive rules 统一使用显式失败语义（`Result[Thm, LogicError]`）。
- 等式构造 `mk_eq` 强制同型输入，拒绝异型等式。
- 签名层包含 scope + theory 双层状态入口，并对 reserved symbol (`=`) 做硬约束。
- `DefHeads` 单调历史与 `TypeDef` fail-closed 门禁已落地到状态 API。
- `SigError` 与 `LogicError` 已统一采用 MoonBit `suberror` 风格定义，错误分类可模式匹配且可扩展。
- `kernel_audit_test.mbt` 已覆盖 Appendix C/D/E 的关键审计场景（定义历史、typedef 见证、多态实例、typed de Bruijn 守卫）。

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
moon info
moon fmt
```

备注：当前环境下全仓 `moon test` 可能触发 Moon 编译器 ICE，因此阶段性门禁使用
`moon build + moon test src/kernel`。

## 执行计划

详细分阶段计划见 `PLAN.md`。
