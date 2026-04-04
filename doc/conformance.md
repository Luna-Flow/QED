# QED Conformance

本文档记录当前 MoonBit 工程线怎样对齐 `doc/qed_formal_spec.pdf`，以及外围工程怎样才算符合现在的核心。

它不是新的规范层；它的作用是把“论文要求”“当前代码”“当前测试”“外围工程义务”放到同一张表上。

## Normative Source

QED 当前的权威关系如下：

- `doc/qed_formal_spec.pdf` 是唯一规范性来源。
- `doc/qed_formal_spec.typ` 是规范源文件。
- `doc/manual.md` 描述当前仓库中的实现合同。
- 本文档描述工程符合性、代码/测试映射和外围工程 checklist。

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
- theorem admissibility around const identity、schema instance 和 definitional coherence
- resolved elaboration boundary with frozen constant identity
- parser normalize + raw-offset contract
- surface connector 的 basis-backed lowering contract
- audit certificates 与 executable conservative replay hook
- logic 层的 definition theorem / unfold / replay helper

### Implemented But Intentionally Partial

以下部分已经存在，但覆盖范围仍有限（M1：已支持战术子集可回放为内核 `Thm`，其余路径 fail-closed）：

- `tactics` 的 `Goal` / `ProofState` / step execution 与 `ps_qed` 成功路径
- `prover` 的 linear theorem-script driver

这些层尚不是“任意用户证明都能产出可信 theorem”的完整前端。

### Not Implemented

当前没有实现，应明确视为缺失能力的部分包括：

- dictionary passing
- typeclass frontend
- instance environment / instance search
- constraint solving
- metavariables / holes
- local type inference
- higher-order unification
- richer proof blocks
- 任意脚本 / 任意战术组合下的完备 theorem reconstruction（当前仅为已测试子集）

## Code And Test Mapping

| Area | Current implementation | Regression coverage |
| --- | --- | --- |
| Typed core + boundary conversion | `src/kernel/types.mbt`, `src/kernel/terms.mbt` | `src/kernel/kernel_terms_test.mbt`, `src/kernel/kernel_types_test.mbt` |
| Scoped state + extension gates | `src/kernel/sig.mbt` | `src/kernel/kernel_sig_test.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Primitive rules + admissibility | `src/kernel/thm.mbt` | `src/kernel/kernel_thm_test.mbt`, `src/kernel/kernel_thm_wbtest.mbt`, `src/kernel/kernel_audit_test.mbt` |
| Resolved elaboration boundary | `src/elab/resolved.mbt` | `src/elab/elab_test.mbt` |
| Parser bridge + normalize/raw-offset contract | `src/parser/parser.mbt` | `src/parser/parser_test.mbt` |
| Surface connector basis expansion | `src/logic/prop_prelude.mbt`, `src/logic/prop_foundation.mbt`, `src/logic/prop_tools.mbt` | `src/logic/prop_prelude_test.mbt`, `src/logic/prop_tools_test.mbt`, `src/parser/parser_test.mbt` |
| Operational proof scripting + M1 replay | `src/tactics/proof_state.mbt`, `src/logic/prop_replay.mbt`, `src/prover/prover.mbt` | `src/tactics/proof_state_test.mbt`, `src/tactics/tactics_test.mbt`, `src/prover/prover_test.mbt`, `src/logic/prop_replay_test.mbt` |
| Formal Part I / Part II conformance pack | `formal_verification/QEDFV/Audit/PartI.lean`, `formal_verification/QEDFV/Engineering/Conformance.lean` | `lake build` |

值得特别注意的回归点：

- `src/kernel/kernel_audit_test.mbt` 已覆盖 def-head monotonicity、typedef witness validity、const-id drift、typed beta/trans guard、conservative replay 等高风险场景。
- `src/prover/prover_test.mbt` 对 M1 已覆盖的正例断言 `prove_theorem_script` 返回 `Ok` 且结论可用 `thm_concl` 核对；不支持的路径仍须诚实失败。

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

- `logic` 只能做 checked wrapper、definition/unfold helper 和 replay helper；不能绕过 kernel invent 新规则。
- `parser` 必须保持 `local > const`、normalize + raw-offset contract，并与 `logic` 共用同一套 connector contract。
- `elab` 必须冻结 resolved identity；后续 typing 遇到 const-id 或 schema drift 时必须 fail-closed。
- `tactics` 在通过 `logic` 回放构造出与相继式一致的 `Thm` 时，方可由 `ps_qed` 交出定理；否则须 fail-closed。
- `prover` 仅在回放成功时返回 `Ok` 与 `Thm`；否则必须继续返回诚实错误（含 `ProofSynthesisUnavailable`）。
- extension certificate 只能是 audit artifact；不能被当成 theorem acceptance 的替代物。

这组 checklist 的目标，是把可执行前端逐步压成论文里所说的 faithful realization，而不是在外围工程里新增第二套逻辑系统。

## Peripheral Alignment

当前工作区中正在形成的主线，应当理解为一次有意识的工程收口：

- parser 正在从“依赖 state 中存在同名 prelude 常量”切向“直接 basis expansion，再走 resolve/lowering contract”。
- logic 正在从“注册符号名”切向“定义常量 + definition theorem + unfold/replay helper”。
- prover 测试已经接受“即使不自动安装 prelude，也仍然 fail-closed 到 proof synthesis unavailable”，说明系统正在把 connector 语义与 theorem synthesis 责任拆开。

如果外围工程要继续符合现在的核心，下一步仍应扩展：

- connector replay builders 与战术覆盖
- `ProofState` 的证据字段与 QED 校验（向更大脚本面推进）
- 更多 `prove_theorem_script` end-to-end 回归

这些任务应当复用现有工具：

- `logic_prop_def_*`
- `logic_prop_unfold_*`
- `logic_apply_fun_eq*`
- `logic_beta_normalize_eq`
- `logic_eq_mp_bool`
- `logic_eq_sym`

不应该另起一套仅在 tactic/prover 中成立、但无法 replay 到 kernel path 的临时证明语义。

## Current Gaps

当前仍然存在的主要缺口有：

- MoonBit 前端尚无可覆盖任意用户证明的 end-to-end faithful realization witness。
- `ProofState` 的证据与战术覆盖仍在 M1 子集阶段。
- `ps_qed` / `prove_theorem_script` 对未支持输入仍不重建 `Thm`。
- dictionary passing / typeclass runtime 仍未落地。
- 当前仓库尚无稳定 `cmd` 用户接口；后续命令行层需要作为新的非权威外围集成重新引入。

所以更准确的状态判断是：

- Part I 核心与 Part II 的主要符合性口径已经落地；
- 外围工程正在向 faithful realization 收束；
- 但 theorem-producing frontend 还没有完成。

## Verification Gate

当前推荐的 paper-alignment / engineering-conformance 门禁是：

```bash
moon build
moon test src/kernel
moon test
cd formal_verification
lake build
```

2026-04-04 本地核对结果：

- `moon test` 通过
- `lake build` 通过

当涉及 trust boundary、scope、gate、connector contract 或 proof scripting 语义时，应同时检查：

- `doc/manual.md`
- `doc/qed_formal_spec.pdf`
- 本文档
