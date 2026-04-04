# QED（Quite Easy Deduction）

QED 是一个基于 MoonBit 的 theorem prover 项目，采用 kernel-first 设计。

- MoonBit 实现线负责可执行、可测试的可信内核与受控前端。
- Lean 4 形式化线负责对论文规范做语义对齐、审计与符合性封板。

唯一规范性来源是 `doc/qed_formal_spec.pdf`（源文件：`doc/qed_formal_spec.typ`）。

## 当前状态

- `src/kernel` 已提供 opaque `Thm`、checked primitive rules、scoped signature state，以及 `DefOK` / `TypeDefOK` / `SpecOK` gate。
- `src/kernel` 当前会在 theorem admission、sentence-in-language 和 theory admission 边界上拒绝超出当前 `Sigma_t` 的 ghost type constructor。
- `src/elab` 已实现 resolved elaboration boundary，冻结 `const_id + schema_ty + inst_ty`，并在后续 typing 中拒绝 scope drift。
- `src/parser` 当前先做输入 normalize，再执行 `SynTerm -> RTerm -> Term` 桥接；`ParseError.offset` 仍对原始输入负责。
- `src/logic` 当前把表面连接词统一收口到 basis-backed proposition term、canonical definition theorem，以及 state-backed trusted connector recognition。
- `src/tactics` / `src/prover` 目前仍是 fail-closed 原型：可以执行 goal transformation，但还不会伪造最终 kernel theorem。
- `formal_verification/` 已包含 Part I / Part II 的 conformance 与 transfer 证明链。

## 仓库结构

```text
QED/
├── src/
│   ├── kernel/              # Trusted kernel
│   ├── logic/               # Checked wrappers + connector/replay helpers
│   ├── elab/                # resolved elaboration boundary
│   ├── parser/              # text frontend + bridge
│   ├── tactics/             # operational proof-state engine
│   └── prover/              # theorem-script driver (fail-closed)
├── formal_verification/
│   └── QEDFV/               # Lean 4 formalization and audit pack
├── doc/
│   ├── manual.md            # 当前实现合同
│   ├── conformance.md       # 论文对齐与外围工程符合性
│   ├── qed_formal_spec.pdf  # 规范正文（normative source）
│   └── qed_formal_spec.typ  # 规范源文件
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

2026-04-04 本地核对结果：

- `moon test` 通过
- `formal_verification/lake build` 通过

## 文档地图

- `doc/qed_formal_spec.pdf`：唯一规范性来源。
- `doc/manual.md`：当前实现合同，面向贡献者，描述真实边界、模块职责和当前能力。
- `doc/conformance.md`：论文对齐、代码/测试映射、Part II conformance obligations、外围工程 checklist。
- `doc/qed_formal_spec.typ`：规范源文件。

`doc/` 下其余专题文件当前只保留为跳转页或作者内部笔记，不再作为贡献者的一线入口。

## 工程约定

- 保持 kernel 为唯一 theorem-construction boundary。
- 上层模块不得引入新的逻辑权威，只能构造、冻结、调度或 replay kernel 已检查的路径。
- 与语义、gate、scope、boundary 相关的改动，应同时更新实现、测试和必要的形式化材料。

## License

Apache-2.0（见 `LICENSE`）。
