# QED (Quite Easy Deduction)

QED 是一个基于 MoonBit 的交互式定理证明器，目标是在 MoonBit 生态中提供可扩展、可验证的形式化推理基础设施。

## 标准目标

项目当前以以下目标作为统一标准：
- 可信内核：基于 LCF 架构，保证定理对象仅由内核规则构造。
- 逻辑表达：实现 STT/HOL 的核心类型、项与推理能力。
- 可用性：提供 tactic 驱动的证明流程与最小 CLI 入口。
- 工程质量：以测试与接口变更检查为准绳持续迭代。

## 当前范围

`In Scope`：
- `kernel`：`hol_type`/`term`/`thm` 与原始规则。
- `logic`：基础逻辑连接词与核心引理。
- `tactics`：`Goal`、基础 tactics、tacticals。
- `cmd`：最小 proof check 命令行能力。

`Out of Scope（当前阶段）`：
- 完整数学库。
- 高级语法宏与大规模自动化。

## 项目结构

```text
src/
├── kernel/     # Trusted Kernel
├── logic/      # Logical foundations
├── tactics/    # Tactic engine
└── cmd/        # CLI entry (planned)
```

## 开发命令

```bash
moon build
moon test
moon info
moon fmt
```

建议在任务收尾统一执行：

```bash
moon info && moon fmt && moon test
```

## 执行计划

详细里程碑、验收标准与 Agent 工作协议见：`PLAN.md`。
