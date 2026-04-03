# QED（Quite Easy Deduction）

QED 是一个基于 MoonBit 的 theorem prover 项目，采用 **kernel-first** 设计：

- 运行时实现线（MoonBit）：负责可执行、可测试的可信内核与上层封装。
- 形式化验证线（Lean 4）：负责对论文规范进行机器化语义对齐、证明与审计封板。

规范基线：`doc/qed_formal_spec.pdf`（源文件：`doc/qed_formal_spec.typ`）。

## 仓库结构

```text
QED/
├── src/
│   ├── kernel/      # Trusted kernel（types/terms/signature/theorem + tests）
│   ├── logic/       # 逻辑层封装
│   ├── elab/        # named elaboration -> resolved term -> lowering 边界层
│   ├── parser/      # Parser v0.5（term/goal/theorem-by raw + resolved bridge）
│   ├── tactics/     # ProofState + tactic 执行层
│   ├── prover/      # theorem-by 脚本编排入口
│   └── cmd/         # 命令行入口与集成测试
├── formal_verification/
│   ├── QEDFV/       # Lean 4 形式化（Part I/II 语义对齐）
│   ├── lakefile.toml
│   └── lean-toolchain
├── doc/
│   ├── elab_boundary.md
│   ├── parser_v0.md
│   ├── qed_formal_spec.typ
│   ├── qed_formal_spec.pdf
│   ├── qed_formal_spec_changelog.md
│   └── kernel_paper_traceability.md
├── moon.mod.json
└── README.md
```

## 环境要求

### MoonBit 实现线

- 安装 MoonBit 工具链（`moon`）。

### Lean 形式化线

- 安装 Lean 工具链管理器（`elan`）。
- `formal_verification/lean-toolchain` 固定 Lean 版本。
- `formal_verification/lakefile.toml` 管理 Lean 依赖（含 mathlib）。

## 快速开始

### 1) MoonBit 构建与测试

```bash
# 仓库根目录
moon build
moon test src/kernel
moon test
```

### 2) MoonBit 提交前维护命令

```bash
# 仓库根目录
moon info
moon fmt
```

推荐提交前门禁：

```bash
moon info && moon fmt && moon test
```

### 3) Lean 形式化构建

```bash
cd formal_verification
lake build
```

## 当前实现进度（截至当前主分支）

### A. MoonBit 实现线

- kernel 可信边界已成型：核心规则以 checked/stateful 语义对外。
- `src/kernel` 测试体系覆盖基础行为、审计回归与白盒边界检查。
- `logic / tactics / prover / cmd` 已形成可运行的上层链路，其中 `tactics/prover` 当前是 fail-closed 的脚本与 goal 执行原型。
- `elab` 已提供 resolved elaboration boundary + typed builders：
  - `elab_const / elab_const_instance / elab_app / elab_abs / elab_eq`
  - `RTerm / ElabCtx / ElabError`
  - `elab_resolve_named_term / elab_core_type_of / elab_lower_to_term / elab_lower_to_db`
  - 命题判定：`elab_is_prop / elab_require_prop`
- `parser` v0.5 已落地并可桥接到现有层：
  - `parse_term_raw / parse_goal_raw / parse_theorem_script_raw`
  - `parse_term(state, src) / parse_goal(state, src)`
  - `parse_resolved_term_with_env / parse_term_with_env / parse_goal_with_env / parse_let / parse_def_function`
  - 支持语法：`Name`、空格应用、`¬/->/∧/∨/=`（含 `\not/\imp/\and/\or`）、括号、`H1, H2 |- C`、`H1, H2 ⊢ C`、`let x : T`、`def f(x : A) : B { body }`
  - `=` 当前为 non-assoc（`a = b = c` 会报错）
- `tactics` 已提供 ProofState 与核心 7 个 step：`intro/exact/apply/assumption/split/left/right`，用于 goal-state 变换。
- `prover` 已提供 `prove_theorem_script`：可解析并执行线性 `theorem ... := by ...` 脚本，并在 theorem synthesis 尚未实现时 fail-closed（可自动安装命题 prelude）。

### B. Lean 形式化线（QEDFV）

- 已完成 Part I/II 主干语义对齐与证明链闭环。
- 构造性闭包已具备：Derivation Object + 三类 Erasure + finite-step conservativity 组合。
- conformance 侧已强化到 replay 语义（含 primitive-instance replay 对齐）。
- 已完成 release freeze 语义封板：
  - `Spec.Items.RELEASE_FREEZE_GATE_proved`
  - `Audit.PartI.final_verification_complete_proved`
- 当前状态：`formal_verification` 下 `lake build` 全绿。

## 工程约定

- 保持 kernel 边界最小且可审计，优先 checked/stateful 接口。
- 扩展与规则路径保持 fail-closed。
- 语义相关改动需同步更新：
  - `src/` 的实现与测试
  - `formal_verification/QEDFV/` 的形式化与审计条目

## 文档索引

- 规范正文：`doc/qed_formal_spec.pdf`
- 规范源：`doc/qed_formal_spec.typ`
- 规范变更记录：`doc/qed_formal_spec_changelog.md`
- 章节追溯：`doc/kernel_paper_traceability.md`
- Elab 边界设计：`doc/elab_boundary.md`
- Parser v0 语法与接口：`doc/parser_v0.md`
- 用户手册（含 HOL 入门）：`doc/manual.md`

## Roadmap（待与你确认后细化）

- 当前 README 先保留稳定版进度说明。
- Roadmap 章节将基于你的优先级（实现线 / 形式化线 / 交付节奏）单独讨论后更新。

## License

Apache-2.0（见 `LICENSE`）。
