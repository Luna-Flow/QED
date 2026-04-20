# QED Conformance

Status: active
Audience: contributors, reviewers
Authority: engineering conformance guide; subordinate to `doc/qed_formal_spec.pdf` and current code/tests
Scope: code/test mapping, implementation alignment, contributor obligations, and documentation example rules
Last reviewed: 2026-04-20

本文档记录当前 MoonBit 工程线怎样对齐 `doc/qed_formal_spec.pdf`，以及外围工程怎样才算符合现在的核心。

它不是新的规范层；它的作用是把“论文要求”“当前代码”“当前测试”“外围工程义务”放到同一张表上。

## Normative Source

QED 当前的权威关系如下：

- `doc/qed_formal_spec.pdf` 是唯一规范性来源。
- `doc/qed_formal_spec.typ` 是规范源文件。
- 当前代码与测试决定当前真实 shipped state。
- `doc/governance.md` 规定文档层级与引用规则。
- `doc/manual.md` 描述当前仓库中的实现合同。
- 本文档描述工程符合性、代码/测试映射和贡献者 checklist。

Part II conformance 相关的 Lean 锚点主要在：

- `formal_verification/QEDFV/Engineering/Conformance.lean`
- `formal_verification/QEDFV/Spec/Items.lean`
- `formal_verification/QEDFV/Audit/AppendixG.lean`
- `formal_verification/QEDFV/Audit/PartI.lean`

## Implemented vs Not Implemented

### Implemented And Tested

当前已经有稳定代码与回归测试支撑的部分包括：

- typed term/type core
- opaque theorem object + checked primitive rules
- scoped signature stack 与 definition history discipline
- `DefOK` / `TypeDefOK` / `SpecOK` gate
- theorem admissibility around const identity、schema instance、definitional coherence 和 type-language admissibility
- resolved elaboration boundary with frozen constant identity
- parser normalize + raw-offset contract
- parser-owned goal lowering boundary without direct tactics dependency
- surface connector 的 basis-backed lowering contract
- canonical definition-theorem-backed connector recognition
- audit certificates 与 executable conservative replay hook
- logic 层的 definition theorem / unfold / replay helper
- supported propositional theorem scripting paths that replay to kernel `Thm`

### Implemented But Intentionally Partial

以下部分已经存在，但覆盖范围仍有限：

- `tactics` 的 `Goal` / `ProofState` / step execution 与 `ps_qed` 成功路径
- `prover` 的 theorem-script driver
- theorem-name based replay 目前只覆盖小规模稳定命题目录
- parser 当前支持 theorem-header binder、顺序 `by` body 与最小结构化分支块语法：
  theorem 头部可带零个或多个 `(name : type)` binder；
  body 可写成单行 `theorem ... := by step; step; ...`，
  或块状 `theorem ... := by` 后按换行分隔的 step 列表；
  `split` / `left` / `right` 仍可携带最小 branch block 语法，并保留
  raw binder/goal/step span；branch body 的实际调度与 blame 归因由 `prover` 负责
- theorem-script 当前还支持 `hole` / `hole <name>` unfinished-proof step；
  theorem-header binder 当前已构成 shipped quantifier-facing surface，能够稳定进入
  goal lowering、proof-state locals 与 cmd diagnostics；raw `forall` / `∀`
  theorem goal 也作为 goal-only sugar 进入 shipped lowering path，但仍不是 term-level syntax
- parser-side `parse_let` / `parse_def_function` 已 formalize 为 non-script utility surface

这些层不是“任意用户证明都能产出可信 theorem”的完整前端。

### Not Implemented

当前没有实现，应明确视为缺失能力的部分包括：

- richer proof blocks
- promoted rewrite/simplify tactic / command surface
- dictionary passing
- typeclass frontend
- instance environment / instance search
- constraint solving
- metavariables / holes
- local type inference
- higher-order unification
- 任意脚本 / 任意战术组合下的完备 theorem reconstruction

## Code And Test Mapping

| Area | Current implementation | Regression coverage |
| --- | --- | --- |
| Typed core + boundary conversion | `src/kernel/types.mbt`, `src/kernel/terms.mbt` | `src/kernel/kernel_terms_test.mbt`, `src/kernel/kernel_types_test.mbt` |
| Scoped state + extension gates | `src/kernel/sig.mbt` | `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Primitive rules + admissibility | `src/kernel/thm.mbt` | `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Resolved elaboration boundary | `src/elab/resolved.mbt` | `src/elab/elab_test.mbt` |
| Parser bridge + normalize/raw-offset contract | `src/parser/parser.mbt` | `src/parser/parser_test.mbt` |
| Parser-to-tactics explicit goal bridge | `src/parser/parser.mbt`, `src/prover/prover.mbt` | `src/parser/parser_test.mbt`, `src/prover/prover_positive_corpus_test.mbt` |
| Surface connector basis expansion | `src/logic/prop_prelude.mbt`, `src/logic/prop_foundation.mbt`, `src/logic/prop_tools.mbt` | `src/logic/prop_prelude_test.mbt`, `src/logic/prop_tools_test.mbt`, `src/parser/parser_test.mbt` |
| Proposition theorem replay/catalog seeds | `src/logic/prop_bool_theorems.mbt`, `src/logic/prop_refs.mbt`, `src/logic/prop_replay.mbt` | `src/logic/prop_bool_theorems_test.mbt`, `src/logic/prop_refs_test.mbt`, `src/logic/prop_replay_test.mbt` |
| Operational proof scripting + M1 subset replay | `src/tactics/proof_state.mbt`, `src/prover/prover.mbt` | `src/tactics/proof_state_test.mbt`, `src/tactics/tactics_test.mbt`, `src/prover/prover_test.mbt`, `src/prover/prover_positive_corpus_test.mbt`, `src/prover/prover_negative_corpus_test.mbt` |
| File-first `cmd` integration surface | `src/cmd/cmd.mbt` | `src/cmd/cmd_wbtest.mbt` |
| Quantifier-facing binder / raw-`forall` corpus + CLI contract | `src/prover/corpus.mbt`, `src/prover/prover_mapping_matrix_test.mbt`, `src/cmd/cmd_corpus_wbtest.mbt` | `src/cmd/cmd_corpus_wbtest.mbt`, `src/cmd/cmd_wbtest.mbt`, `src/prover/prover_mapping_matrix_test.mbt` |
| Formal Part I / Part II conformance pack | `formal_verification/QEDFV/Audit/PartI.lean`, `formal_verification/QEDFV/Engineering/Conformance.lean` | `lake build` |

值得特别注意的回归点：

- `src/kernel/kernel_audit_test.mbt` 已覆盖 def-head monotonicity、typedef witness validity、const-id drift、typed beta/trans guard、conservative replay 等高风险场景。
- `src/parser/parser_test.mbt` 已覆盖 normalize/raw-offset contract 与非 `bool` connector 的 fail-closed rejection。
- `src/parser/parser_test.mbt` 当前也覆盖 theorem-header binder、structured
  branch block 解析，以及 raw-span 回归。
- `src/parser/parser_test.mbt` 与 `src/prover/prover_positive_corpus_test.mbt`
  当前共同固定 parser-owned goal lowering 与上层显式 bridge 到 `tactics.Goal` 的合同。
- `src/prover/prover_test.mbt` 当前固定 structured branch block 的脚本调度、branch path
  归因与 step blame 口径。
- `src/prover/prover_test.mbt` 当前覆盖了 M1 已支持子集的 `Ok((KernelState, Thm))` 正例，以及若干 direct-close / implication-backed theorem-name path。
- `src/prover/prover_positive_corpus_test.mbt` / `src/prover/prover_negative_corpus_test.mbt`
  当前承载 shipped subset 的 canonical script corpus，用于固定 capability
  覆盖与 honest failure 口径。
- `src/prover/prover_test.mbt`、`src/prover/prover_mapping_matrix_test.mbt` 与
  `src/cmd/cmd_corpus_wbtest.mbt` 当前也覆盖了 unfinished-proof / hole reporting
  的结构化合同与 canonical unfinished corpus 锚点。
- `src/prover/prover_mapping_matrix_test.mbt` 与 `src/cmd/cmd_corpus_wbtest.mbt`
  当前也覆盖了 nested branch unfinished path 与 stable empty-marker rendering。
- `src/cmd/cmd_corpus_wbtest.mbt` 与 `src/cmd/cmd_wbtest.mbt` 当前也固定了 shipped
  quantifier-facing binder / raw-`forall` scripts 的 success / failure /
  unfinished CLI contract，包括 goal、locals、branch path 与 step blame。
- `src/prover/prover_mapping_matrix_test.mbt` 当前把 positive / negative /
  unfinished 三类 canonical case id、量词 binder / raw-`forall` case id、能力标签与
  `doc/manual.md` 的公开示例锚点绑定在同一份回归约束里。
- `src/cmd/cmd_wbtest.mbt` 当前覆盖 success rendering、parse/io/usage failure、
  tactic failure context rendering、branch-path rendering，以及 file-first argv
  workflow。

### Documentation Example Source Contract

为避免文档把规划能力写成已交付能力，当前文档示例必须遵守以下来源约束：

- `README.md` 只发布当前 shipped subset 的摘要，不单独发明新示例语义。
- `doc/manual.md` 中的 runnable theorem-script examples 必须来自现有回归测试覆盖。
- theorem-producing 正例脚本当前以
  `src/prover/prover_test.mbt` 与 `src/prover/prover_positive_corpus_test.mbt`
  为主锚点。
- shipped subset 的负例 / honest failure 示例当前以
  `src/prover/prover_negative_corpus_test.mbt` 为主锚点。
- canonical unfinished-proof 示例当前以
  `src/prover/prover_test.mbt`、`src/prover/prover_mapping_matrix_test.mbt`
  与 `src/cmd/cmd_corpus_wbtest.mbt` 为主锚点；root-level unfinished 与 nested
  branch unfinished 两类样例都要保持同步。
- quantifier-facing binder / raw-`forall` 示例当前也以
  `src/prover/corpus.mbt`、`src/prover/prover_mapping_matrix_test.mbt` 与
  `src/cmd/cmd_corpus_wbtest.mbt` 为主锚点；公开文档只允许引用这些 canonical
  case id。
- 公开文档中的 case-id 到示例锚点映射当前以
  `src/prover/prover_mapping_matrix_test.mbt` 为主锚点。
- tactic-level 例子、local-over-name 冲突与 wrong-mode honest failure 当前以
  `src/tactics/proof_state_test.mbt` 为主锚点。
- 若文档要新增、修改或删除公开示例，应同步新增、修改或删除对应回归测试。

## Part II Conformance Obligations

Lean 中当前已经把外围工程的 Part II obligations 明确写成了工程义务。核心项包括：

- `ruleFidelity`
- `boundaryFidelity`
- `scopeFidelity`
- `replayTraceFidelity`
- `gateFidelity`
- `certificateNonAuthority`
- `conservativeReplayFidelity`

对贡献者来说，更可执行的 checklist 是下面这组规则。

### Contributor Checklist

- `logic` 只能做 checked wrapper、definition/unfold helper、replay helper 和非权威 theorem reference 组织；不能绕过 kernel invent 新规则。
- `parser` 必须保持 `local > const`、normalize + raw-offset contract，并与 `logic` 共用同一套 connector contract。
- `elab` 必须冻结 resolved identity；后续 typing 遇到 const-id 或 schema drift 时必须 fail-closed。
- `tactics` 只能在通过 `logic` 回放构造出与相继式一致的 `Thm` 时，由 `ps_qed` 交出定理；否则必须 fail-closed。
- `ps_qed` 的最终验收当前必须按 strict normalized sequent equality 执行；不得保留仅按
  shape-aware compatibility 放行的旧边界。
- `prover` 仅在回放成功时返回 `Ok` 与 `Thm`；否则继续返回诚实错误。
- `cmd` 只能是新的非权威集成层，不得成为第二证明内核。
- extension certificate 只能是 audit artifact；不能被当成 theorem acceptance 的替代物。

这组 checklist 的目标，是把可执行前端逐步压成论文里所说的 faithful realization，而不是在外围工程里新增第二套逻辑系统。

## Peripheral Alignment

当前工作区的工程主线是一次有意识的收口：

- parser 已从“依赖 state 中存在同名 prelude 常量”转为“basis-backed builder + resolve/lowering contract”。
- logic 已从“注册表面符号名”推进到“定义常量 + definition theorem + unfold/replay helper + 小型 theorem catalog + shared theorem inventory”。
- tactics/prover 已从纯 operational prototype 前进到“支持子集可 replay 到 kernel `Thm`，并由 canonical corpus 固定支持矩阵与 honest failure”。

若外围工程要继续符合现在的核心，应继续保持：

- 在共享 theorem inventory 与 canonical corpus 之上继续扩展 replay builders；
- 继续把新 shipped capability 写回 canonical corpus / mapping matrix /
  manual anchors，避免文档口径落后于实现；
- 把 goal / hole / unfinished-proof diagnostics 做成正式前端合同，但继续明确它们
  不是 proof object；
- 对 theorem-header binder 这条已 shipped 的 quantifier-facing 路径，以及 raw `forall`
  theorem-goal sugar，继续保持 parser/lowering/replay 的边界显式化；
- 让 `cmd` 继续复用 `prover` 的 structured failure contract，而不是自行解释错误字符串；
- 在当前 file-first workflow 之上继续扩大前端表达力。

这些任务应当复用现有工具：

- `logic_prop_def_*`
- `logic_prop_unfold_*`
- `logic_apply_fun_eq*`
- `logic_beta_normalize_eq`
- `logic_eq_mp_bool`
- `logic_eq_sym`
- `logic_prop_replay_*`

不应该另起一套仅在 tactic/prover 中成立、但无法 replay 到 kernel path 的临时证明语义。

## Remaining Non-Shipped Surfaces

当前仍然没有 shipped 的能力包括：

- theorem catalog 仍然偏小，尚不足以支撑更自然的大量脚本；但当前 shipped subset
  的 inventory、mode 边界与 corpus 已经固定；
- canonical corpus 还需要补齐 hardening regression，才能完成 `H5` 集成门；
- theorem-script body 已支持最小 `M4b` 结构化分支块；但 richer proof block
  仍未实现；
- holes / unfinished proof 当前已进入 shipped theorem-script surface；但 hole
  completion / metavariable authority 仍未实现；
- theorem-header binder 这条 quantifier-facing surface 已 shipped；raw
  `forall` / `∀` theorem-goal frontend 也已作为 goal-only sugar 支持；
- parser-side utility surface 已收口为 non-script API；后续只需保持文档 / 测试同步；
- Lean 线当前是 paper/conformance pack，而不是 MoonBit 源码的直接机械化证明。

因此更准确的状态判断是：

- Part I 核心与 Part II 的主要符合性口径已经落地；
- 支持子集上的 theorem-producing frontend 已经存在；
- 但更完整的 faithful realization 仍在继续收口。

## Verification Gate

当前推荐的 paper-alignment / engineering-conformance 门禁是：

```bash
moon build
moon test
cd formal_verification
lake build
```

准备合并或封板时，还应执行：

```bash
moon info
moon fmt
moon test
cd formal_verification
lake build
```

2026-04-05 本地核对结果：

- `moon test` 通过
- `lake build` 通过

当涉及 trust boundary、scope、gate、connector contract、proof scripting 或文档口径时，应同时检查：

- `doc/qed_formal_spec.pdf`
- `doc/manual.md`
- 本文档
