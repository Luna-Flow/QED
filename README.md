# QED（Quite Easy Deduction）

QED 是一个基于 MoonBit 的 theorem prover 项目，采用 kernel-first 架构。

- MoonBit 实现线负责可执行、可测试的可信内核与受控前端。
- Lean 4 形式化线负责对论文规范做语义对齐、审计与符合性封板。

唯一规范性来源是 `doc/qed_formal_spec.pdf`（源文件：`doc/qed_formal_spec.typ`）。
当前文档治理规则见 `doc/governance.md`。

## 当前状态

- `src/kernel` 已提供 checked primitive rules、scoped signature state，以及
  `DefOK` / `TypeDefOK` / `SpecOK` gate。
- `src/parser` / `src/tactics` / `src/prover` 已支持受限命题子集的 theorem-script
  replay；不支持路径继续 fail-closed。
- 当前 theorem-script 支持 theorem header binder + 顺序 `by` 块。
- `src/cmd` 已提供 file-first 单文件入口，并复用 prover 的结构化失败载荷。
- `formal_verification/` 当前提供的是 paper-first conformance pack，而不是对
  MoonBit 源码的直接机械化等价证明。

完整实现合同、支持矩阵、示例和失败语义见 `doc/manual.md`。

## 仓库结构

```text
QED/
├── src/
│   ├── kernel/              # Trusted kernel
│   ├── logic/               # Checked wrappers + replay helpers + theorem catalog seeds
│   ├── elab/                # Resolved elaboration boundary
│   ├── parser/              # Text frontend + bridge
│   ├── tactics/             # Proof-state execution engine
│   ├── prover/              # Theorem-script driver
│   └── cmd/                 # File-first CLI surface
├── formal_verification/
│   └── QEDFV/               # Lean 4 formalization and audit pack
├── doc/
│   ├── governance.md        # 文档分层、命名与引用规则
│   ├── manual.md            # 当前实现合同
│   ├── conformance.md       # 论文对齐与外围工程符合性
│   ├── current_workspace_audit.md # 当前阶段的风险与缺口
│   ├── qed_formal_spec.pdf  # 规范正文（normative source）
│   └── qed_formal_spec.typ  # 规范源文件
├── research/
│   ├── README.md            # 研究文档入口与边界声明
│   └── rewrite-simplify/    # rewrite/simplify 研究线
└── README.md
```

## 构建与验证

MoonBit 线：

```bash
moon build
moon test
```

提交前维护：

```bash
moon info
moon fmt
moon test
```

Lean 形式化线：

```bash
cd formal_verification
lake build
```

2026-04-05 本地核对结果：

- `moon test` 通过
- `formal_verification/lake build` 通过

## 文档地图

- `doc/governance.md`：文档层级、命名、元数据和引用规则。
- `doc/qed_formal_spec.pdf`：唯一规范性来源。
- `doc/manual.md`：当前实现合同与支持矩阵。
- `doc/conformance.md`：代码/测试映射、工程符合性与示例来源约束。
- `doc/current_workspace_audit.md`：当前阶段仍未关闭的风险、缺口和 follow-up。
- `research/README.md`：研究目录入口；研究文档不代表 shipped capability。

## 工程约定

- 保持 `kernel` 为唯一 theorem-construction boundary。
- 上层模块不得引入新的逻辑权威，只能组织、冻结、调度或 replay kernel 已检查的路径。
- 与语义、gate、scope、boundary、proof replay 相关的改动，应同时更新实现、测试和必要文档。
- 对外只宣称当前真实支持的子集，不把规划能力写成已交付能力。

## License

Apache-2.0（见 `LICENSE`）。
