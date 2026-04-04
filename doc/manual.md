# QED Manual

本文档是 QED 当前实现合同。

它以当前仓库工作区中的 MoonBit 与 Lean 代码为准，用来回答三件事：

- 现在真正实现了什么；
- 外围工程当前被允许做什么、不能做什么；
- 下一步应该沿着什么方向继续收口，而不是偏离核心。

## Source-of-Truth Hierarchy

QED 当前有四层信息来源，但权威性不同：

- 规范层：`doc/qed_formal_spec.pdf` 是唯一规范性来源，`doc/qed_formal_spec.typ` 是其源文件。
- 实现合同层：本文档描述当前仓库里的真实实现边界与稳定口径。
- 工程符合性层：`doc/conformance.md` 记录代码/测试映射、Part II conformance obligations，以及外围工程 checklist。
- 作者笔记层：`doc/qed_formal_spec_changelog.md`、`doc/TRICK.md` 等文件保留给论文维护，不是贡献者的主入口。

旧的 `doc/parser_v0.md`、`doc/elab_boundary.md`、`doc/connector_expansion.md` 内容已经收敛到本文档，现仅保留为跳转页。

## Trust Boundary

QED 采用 kernel-first 架构。唯一 theorem-construction boundary 是 `src/kernel`。

- `kernel` 负责类型、项、定理对象、签名状态、primitive rules，以及 `DefOK` / `TypeDefOK` / `SpecOK` gate。
- `logic` 只能是 checked kernel API 的薄封装和 replay helper，不得引入新的 primitive rule authority。
- `elab` 负责 one-shot resolution、resolved/core typing 和 lowering，不负责定义新逻辑。
- `parser` 负责文本语法、normalize、桥接和局部环境管理，不得偷偷改变 connector 语义或 scope 规则。
- `tactics` 负责 goal-state transformation，不拥有 theorem authority。
- `prover` 只是 parser + tactics + kernel 的编排入口；除非能够重建可信 kernel evidence，否则必须 fail-closed。
- 当前仓库不再保留 phase0/demo `cmd` 包；后续若恢复命令行入口，仍必须保持诚实的非权威状态。

包边界上的 `Thm` 仍然是 opaque type；外部调用者使用的是 checked/stateful 接口，而不是内部原始构造器。

## Implemented Kernel

当前内核已经稳定落地的部分包括：

- 类型核心：`bool`、`ind`、`fun(a, b)`、一般 `TyApp` 与 type variable。
- 项边界：对外保留 named `Term`，对内使用 typed `DbTerm` 执行 alpha-invariant 规则核心。
- primitive rule checked 接口：
  - `refl_checked`
  - `assume_checked`
  - `trans_checked`
  - `mk_comb_rule_checked`
  - `abs_rule_checked`
  - `beta_rule_checked`
  - `eq_mp_checked`
  - `deduct_antisym_rule_checked`
  - `inst_type`
  - `inst_checked`
- theorem admissibility 检查：
- theorem const-id 绑定必须与当前 state 一致；
- 常量实例化必须满足 principal schema instance 关系；
- definitional theorem 必须通过 `def_inst_coherent`；
- theorem / sentence 中出现的所有类型都必须属于当前 `Sigma_t`；
- type substitution 必须满足 admissibility gate。
- scoped signature state：
  - `empty_kernel_state`
  - `ks_push_scope`
  - `ks_pop_scope`
  - `ks_add_const`
  - `ks_mk_const`
  - `ks_mk_const_instance`
- extension gates：
  - `ks_define_const`
  - `ks_define_const_thm`
  - `ks_register_type_definition`
  - `ks_specify_const`
- extension discipline 已覆盖的关键约束：
  - def-head monotonicity
  - scope push/pop discipline
  - ghost type variable rejection
  - definition closure / cycle rejection
  - typedef witness validity
  - specification witness validity
- 审计与 replay 辅助接口：
  - `ks_extension_cert_count`
  - `ks_extension_cert_at`
  - `ks_conservative_replay_ok`

这些审计对象只用于 observability 与 conservativity regression，不构成新的 proof object。

## Frontend Contracts

### Resolved Elaboration

当前前端保留三层项表示：

1. named `Term`
2. resolved `RTerm`
3. typed `DbTerm`

`RTerm` 的目的不是替代 kernel term，而是冻结 one-shot resolution 结果。当前 `ResolvedConst` 记录：

- `name`
- `const_id`
- `inst_ty`
- `schema_ty`

这意味着常量在 elaboration 时就被绑定到当时的 kernel identity，后续 `push` / `pop` / shadowing 只影响未来的名字解析，不会回写既有 resolved object。

当前 resolved/core typing 的合同是：

- `RVar` 只按当前局部上下文和显式类型匹配；
- `RConst` 必须继续对应同一 `const_id` 与 `schema_ty`；
- `inst_ty` 必须继续满足 principal schema instance 关系；
- 如果 scope 变化导致 frozen identity 不再可接受，typing 必须 fail-closed，而不是静默重查同名常量。

### Parser

当前 parser 是“文本语法 -> AST -> resolved elaboration -> kernel term/goal”的统一入口。

稳定合同包括：

- 名称解析顺序始终是 `local > const`。
- 输入会先经过 `normalize_parser_input`：
  - `\\not` / `\\and` / `\\or` / `\\imp` 会归一化为规范形式；
  - `|-` 会归一化为 `⊢`；
  - 基础冗余空白会被压缩；
  - 这个阶段不会做 AST 级 pretty print。
- `ParseError.offset` 仍然映射回用户原始输入，而不是归一化后的字符串坐标。
- 规范展示语法以 Unicode 为主：
  - term：`¬`、`∧`、`∨`、`->`、`=`
  - goal：`⊢`
- 兼容输入仍接受：
  - `\\not`、`\\and`、`\\or`、`\\imp`
  - `|-`
- theorem script raw 入口已支持：
  - `theorem <name> : <goal> := by <step>; <step>; ...`

### Surface Connectors

`¬` / `->` / `∧` / `∨` 当前都是 surface connector，不是 kernel primitive logic。

当前统一合同是：

- parser/bridge 在 lowering 时通过 `logic` 层的 basis-backed builder 生成 proposition term；
- `prop_mk_not` / `prop_mk_imp` / `prop_mk_and` / `prop_mk_or` 对非 `bool` 输入必须返回 `LogicError`，不能崩溃；
- 这些 connector 的可信语义基础来自 kernel term、equality `=`、choice `@` 与 checked primitive rules；
- 它们不能在 `tactics` 或 `prover` 中被当成额外的 rule authority；
- parser 不再要求 state 里预先存在普通同名常量，才能解析这些 connector；
- `logic.install_prop_prelude` 只有在当前同名常量已经具备 canonical definition theorem 时才视为幂等成功；同名同型但非 canonical 的占位常量必须拒绝；
- `prop_dest_not` / `prop_dest_imp` / `prop_dest_and` / `prop_dest_or` 当前是 **state-backed trusted recognition**：只承认 canonical basis term 或当前 state 中具备 canonical definition theorem 的 connector 常量。

### Logic Helpers

`src/logic` 当前的角色已经从“仅仅暴露 wrapper”延伸到“为后续 replayable theorem synthesis 准备工具”。

当前稳定可见的辅助能力包括：

- proposition basis term builder：
  - `prop_mk_not`
  - `prop_mk_imp`
  - `prop_mk_and`
  - `prop_mk_or`
- proposition destructor：
  - `prop_dest_not(state, prelude, term)`
  - `prop_dest_imp(state, prelude, term)`
  - `prop_dest_and(state, prelude, term)`
  - `prop_dest_or(state, prelude, term)`
- connector definition theorem / unfolding helper：
  - `logic_prop_def_imp`
  - `logic_prop_def_not`
  - `logic_prop_def_and`
  - `logic_prop_def_or`
  - `logic_prop_unfold_head`
  - `logic_prop_unfold_imp`
  - `logic_prop_unfold_not`
  - `logic_prop_unfold_and`
  - `logic_prop_unfold_or`
- equality lifting / normalization helper：
  - `logic_apply_fun_eq`
  - `logic_apply_fun_eq2`
  - `logic_beta_normalize_eq`
  - `logic_eq_sym`
  - `logic_eq_mp_bool`

这些 helper 的目标是让 future proof synthesis 可以显式 replay kernel-checked path，而不是在前端偷偷增加语义捷径。

## Proof Scripting Status

当前 proof scripting 层在**已支持的战术与 prelude 规则**上会通过 `logic` 回放构造内核 `Thm`；不支持的输入仍 fail-closed，不会伪造定理。

已经实现的对象与入口包括：

- `Goal`
- `ProofState`
- `ps_init`
- `ps_current_goal`
- `ps_goal_count`
- `ps_apply`
- `ps_apply_script`
- `ps_qed`
- `prove_theorem_script`

当前支持的 step 只有：

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`

当前语义边界必须这样理解：

- `tactics` 负责变换未解目标栈；
- `prover` 负责解析 script、建立 goal、执行 step；
- 若目标已空但回放无法构造与根目标相继式一致的 `Thm`，`ps_qed` 仍须返回 `ProofSynthesisUnavailable`（或 `Logic` 等诚实错误）；
- `prove_theorem_script` 必须把失败向上传递，不得伪造 `Thm`。

这不是缺陷伪装，而是当前实现刻意保持的 fail-closed 设计。

## Current Trajectory

当前外围工程正在做的是一次有意识的收口，不是零散漂移。

这条主线可以概括为：

- 把 parser、logic、tactics、prover 统一到同一套 connector contract 上；
- 把 proposition prelude 从“表面符号注册”推进到“definition extension + definition theorem + unfold/replay helper”；
- 让上层未来能够通过 replayable kernel path 产出 theorem，而不是在 tactic 层新增隐式逻辑权威。

按现在的代码走向，后续正确的工程方向应当是：

- 增加 connector replay builders；
- 给 `ProofState` 增加 theorem evidence / continuation；
- 继续扩展战术与回放覆盖，使更多脚本可走通与 M1 相同的 checked 路径；
- 让整个可执行前端越来越接近 Part II 所要求的 faithful realization，而不是在 parser、tactics 或 prover 中引入 ad-hoc proof shortcut。

## Not Implemented

当前明确没有实现的能力包括：

- dictionary passing
- typeclass declaration frontend
- instance environment
- instance search / constraint solving
- 自动字典参数插入
- metavariables / holes
- local type inference
- higher-order unification
- richer theorem-script block syntax
- 接受任意 term 参数的 `exact` / `apply`
- 从任意 `ProofState` / 任意 theorem script 到 kernel `Thm` 的**完备**重建（当前仅为已支持子集）

其中最重要的边界是：论文中的 dictionary passing / lawful axiomatic type classes 仍然是 refinement blueprint，不是当前仓库里的可执行能力。

## Examples

### Parser And Connector Lowering

当前 parser 接受兼容输入，但在内部会先归一化再 bridge：

```moonbit
let st0 = expect_ok(ks_add_const(empty_kernel_state(), "P", bool_ty()))
let st1 = expect_ok(ks_add_const(st0, "Q", bool_ty()))

let t1 = expect_ok(parse_term(st1, "¬ P"))
let t2 = expect_ok(parse_term(st1, "P \\imp Q"))
```

这两个输入都不依赖先在 state 中把 `not` 或 `imp` 作为普通常量手工注册后才能被 parse。

### Theorem Script（M1 子集）

在已安装 prelude 且脚本仅使用已支持战术时，`prove_theorem_script` 可返回 `Ok` 与可信 `Thm`（回归见 `src/prover/prover_test.mbt`）。不支持的脚本仍须 fail-closed，不得伪造 `Thm`。

## Validation Gate

当前贡献者应使用以下门禁核对实现与文档是否一致：

```bash
moon build
moon test
cd formal_verification
lake build
```

2026-04-04 本地核对结果：

- `moon test` 通过
- `lake build` 通过

需要进一步看论文对齐、代码/测试映射和外围工程 checklist 时，请阅读 `doc/conformance.md`。
