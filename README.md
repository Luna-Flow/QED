# QED（Quite Easy Deduction）

QED 是一个基于 MoonBit 的 theorem prover 项目，采用 kernel-first 架构。

- MoonBit 实现线负责可执行、可测试的可信内核与受控前端。
- Lean 4 形式化线负责对论文规范做语义对齐、审计与符合性封板。

唯一规范性来源是 `doc/qed_formal_spec.pdf`（源文件：`doc/qed_formal_spec.typ`）。
当前文档治理规则见 `doc/governance.md`。
代码分层与 alias 入口治理规则见 `doc/code_governance.md`。

## 当前状态

- `src/kernel` 已提供 checked primitive rules、scoped signature state，以及
  `DefOK` / `TypeDefOK` / `SpecOK` gate。
- `src/parser` / `src/tactics` / `src/prover` 已支持受限命题子集的 theorem-script
  replay；不支持路径继续 fail-closed。
- 当前 theorem-script 支持 theorem header binder、顺序 `by` 块与最小结构化 branch block。
- theorem-script 当前还支持 `hole`，并会返回结构化 unfinished-proof 结果，而不是伪造 theorem success。
- 量词前端当前支持 theorem-script / goal 位置的 raw `forall` / `∀` 语法糖；term 位置仍不接受。
- `src/cmd` 已提供 file-first 单文件入口，并复用 prover 的结构化失败载荷。
- 当前后续路线已切换到“用户证明体验优先”：优先补齐 script、goal、hole、
  diagnostics 与量词前端，而不是先追求更强自动化。
- `formal_verification/` 当前提供的是 paper-first conformance pack，而不是对
  MoonBit 源码的直接机械化等价证明。

如果你是第一次接触这个项目，建议按下面顺序读文档：

1. `README.md`：项目概览、当前能力边界、如何启动。
2. `doc/manual.md`：用户手册 + 实现合同，包含面向非 HOL 读者的铺垫、简单证明示例、CLI 使用方式和当前支持矩阵。
3. `doc/syntax.md`：当前 theorem-script 输入语法速查，适合查 theorem 头、binder、goal 和 proof step 写法。
4. `doc/conformance.md`：代码/测试如何对齐论文规范，以及贡献者义务。

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
│   ├── code_governance.md   # 包分层、alias 入口与维护规则
│   ├── manual.md            # 用户手册 + 当前实现合同
│   ├── conformance.md       # 论文对齐与外围工程符合性
│   ├── current_workspace_audit.md # 当前阶段的风险与缺口
│   ├── qed_formal_spec.pdf  # 规范正文（normative source）
│   └── qed_formal_spec.typ  # 规范源文件
├── research/
│   ├── README.md            # 研究文档入口与边界声明
│   └── rewrite-simplify/    # rewrite/simplify 研究线
└── README.md
```

## 快速开始

安装好 MoonBit 工具链后，在仓库根目录执行：

```bash
moon build
moon test
```

最简单的 file-first 用法是直接运行仓库里的示例文件，例如：

```bash
moon run src/cmd examples/truth_file.qed
```

对应脚本见 `examples/truth_file.qed`：

```text
theorem truth_file : ⊢ T := by exact truth
```

成功时当前输出形如：

```text
ok truth_file: T
```

如果你没有 HOL 基础，可以先用下面这个直觉理解 QED 的当前子集：

- `⊢ goal` 表示“在没有前提时证明 `goal`”。
- `A ⊢ B` 表示“在假设 `A` 的前提下证明 `B`”。
- `intro` 用于把 `A -> B` 这样的目标转换成“假设一个 `A`，继续证明 `B`”。
- `exact h` 表示“当前目标已经正好由证据 `h` 直接闭合”。
- `split`、`left`、`right` 分别对应“证明合取”“选择证明析取的左支/右支”。

例如，这个脚本表示“假设 `x` 成立，那么 `x ∧ x` 也成立”：

```text
theorem demo_and (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
```

如果你想看一个稍微更像经典数学命题的例子，可以跑这个：

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
```

仓库当前还提供两个最小对照示例：

- `examples/bad_branch.qed`：刻意失败的脚本，演示结构化 `error[...]` 输出。
- `examples/unfinished_branch.qed`：刻意留 `hole` 的脚本，演示 `unfinished ...` 输出。

这类 binder 形式 `(x : bool)` 是当前已 shipped 的量词面入口之一；raw `forall` /
`∀` theorem goal 现在也作为 goal-only sugar 被接受，并沿用同一套 goal lowering、
proof-state locals 与 CLI diagnostics 合同。更多面向初学者的解释和示例见
`doc/manual.md`；如果只是查当前 theorem-script 语法，直接看 `doc/syntax.md`。

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
- `doc/syntax.md`：当前 theorem-script 输入语法速查。
- `doc/code_governance.md`：包分层、alias 入口与代码维护义务。
- `doc/qed_formal_spec.pdf`：唯一规范性来源。
- `doc/manual.md`：用户手册 + 当前实现合同 + 支持矩阵 + honest failure 示例。
- `doc/conformance.md`：代码/测试映射、工程符合性与示例来源约束。
- `doc/current_workspace_audit.md`：当前阶段仍未关闭的风险、缺口和 follow-up。
- `research/README.md`：研究目录入口；研究文档不代表 shipped capability。

## 工程约定

- 保持 `kernel` 为唯一 theorem-construction boundary。
- 上层模块不得引入新的逻辑权威，只能组织、冻结、调度或 replay kernel 已检查的路径。
- `alias.mbt` 是生产源码入口，`alias_test.mbt` 是 blackbox test 镜像入口。
- 与语义、gate、scope、boundary、proof replay 相关的改动，应同时更新实现、测试和必要文档。
- 对外只宣称当前真实支持的子集，不把规划能力写成已交付能力。

## License

Apache-2.0（见 `LICENSE`）。
