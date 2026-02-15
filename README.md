# QED (Quite Easy Deduction)

QED 是一个基于 MoonBit 的交互式定理证明器项目，采用 **kernel-first** 路线，
以 LCF 风格可信边界为核心设计目标。

当前唯一规范源：`doc/qed_formal_spec.pdf`（源文件：`doc/qed_formal_spec.typ`）。

## 项目快照（截至 2026-02-15）

- Stage A（规范冻结）已完成，见 `doc/SPEC_FREEZE_CHECKLIST.md`（记录日期：2026-02-14）。
- kernel 对外保持 checked/stateful 接口；`Thm` 为 opaque 类型，包外不可伪造。
- `DefOK` / `TypeDefOK` / `SpecOK` 三类扩展门禁均已接入状态 API。
- 支持 Infinity Anchor 注册与读取（`ind` 载体 + fail-closed 约束）。
- 支持扩展证书轨迹与保守重放检查：
  - `ks_extension_cert_count`
  - `ks_extension_cert_at`
  - `ks_conservative_replay_ok`
- 错误体系为可模式匹配的 `suberror`：
  - 逻辑层：`LogicError`
  - 签名/扩展层：`SigError`
- 本地验证（2026-02-15）：
  - `moon test src/kernel` -> 106/106 passed
  - `moon test` -> 121/121 passed

## 当前能力边界

### 1) Trusted kernel（已实现）

- 类型与项核心（含 de Bruijn 表示与边界转换）。
- 10 条 primitive rule 的 checked 入口（`*_checked`）。
- 常量定义、类型定义、规格化引入等 gate 的 fail-closed 准入检查。
- 常量身份（const-id）绑定与 theorem admissibility 检查，阻断状态漂移复用。

### 2) 上层封装（可用但仍精简）

- `logic`：对 kernel gate/rule 的稳定包装与语义透传。
- `tactics`：最小策略引擎（当前含 `solve_by_assume`）。
- `cmd`：phase0 冒烟路径（串起 kernel + tactics）。

### 3) 审计与追溯（已接入）

- 章节到实现映射：`doc/kernel_paper_traceability.md`
- 关键审计回归：
  - `src/kernel/kernel_audit_test.mbt`
  - `src/kernel/kernel_thm_wbtest.mbt`

## 目录结构

```text
.
├── src/
│   ├── kernel/   # Trusted kernel: types/terms/sig/thm + audit tests
│   ├── logic/    # Logic wrappers over kernel
│   ├── tactics/  # Minimal tactic layer
│   └── cmd/      # Phase0 CLI integration path
├── doc/
│   ├── qed_formal_spec.typ/pdf
│   ├── kernel_paper_traceability.md
│   ├── SPEC_FREEZE_CHECKLIST.md
│   └── NEXT_STAGE.md
├── formal_verification/  # Lean 4 formalization track (independent workstream)
└── PLAN.md               # Execution plan for current implementation stream
```

## 快速开始

### 环境

- 安装 MoonBit 工具链（本仓库最近一次验证环境：`moon 0.1.20260209`）。

### 常用命令

```bash
# 构建
moon build

# 核心门禁（推荐先跑）
moon test src/kernel

# 全量测试
moon test

# 维护接口与格式（提交前）
moon info
moon fmt
```

推荐提交前门禁：

```bash
moon info && moon fmt && moon test
```

## 文档导航

- 规范正文：`doc/qed_formal_spec.pdf`
- 规范变更记录：`doc/qed_formal_spec_changelog.md`
- kernel 追溯矩阵：`doc/kernel_paper_traceability.md`
- 当前实现计划：`PLAN.md`
- Lean 形式化计划：`formal_verification/PLAN.md`

## 下一阶段重点（简述）

1. 扩展 logic/tactics/cmd 的规则级正反测试，提升跨层可审计性。
2. 持续保持实现与规范双向对账，避免“代码先行、规范缺失”。
3. 固化 CI 门禁（`moon build && moon test src/kernel && moon test`）并扩展 traceability。
