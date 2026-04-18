# QED Manual

Status: active
Audience: contributors, implementers
Authority: implementation contract; subordinate to `doc/qed_formal_spec.pdf` and current code/tests
Scope: current shipped behavior, trust boundary, support matrix, and stable examples
Last reviewed: 2026-04-16

本文档是 QED 当前实现合同。

它以当前仓库工作区中的 MoonBit 与 Lean 代码为准，用来回答三件事：

- 现在真正实现了什么；
- 外围工程当前被允许做什么、不能做什么；
- 下一步应该沿着什么方向继续收口，而不是偏离核心。

## Source-of-Truth Hierarchy

QED 当前采用 `doc/governance.md` 定义的文档层级。对实现合同而言，相关顺序是：

1. `doc/qed_formal_spec.pdf` 是唯一规范性来源，`doc/qed_formal_spec.typ`
   是其源文件。
2. 当前代码与回归测试决定“真实 shipped state”。
3. 本文档与 `doc/conformance.md` 描述当前实现合同与工程符合性。
4. `README.md`、`application.typ` 只做对外摘要，不高于上述层级。
5. `research/` 仅记录未 shipped 的设计研究，不构成产品合同。

若实现与文档冲突，先以代码 + 测试核定真实状态，再回写文档。
若实现与论文规范冲突，论文规范仍为准。

## Trust Boundary

QED 采用 kernel-first 架构。唯一 theorem-construction boundary 是 `src/kernel`。

- `kernel` 负责类型、项、定理对象、签名状态、primitive rules，以及
  `DefOK` / `TypeDefOK` / `SpecOK` gate。
- `logic` 只能是 checked kernel API 的薄封装、definition/unfold helper、
  replay helper 和非权威 theorem reference 组织层，不得引入新的 primitive
  rule authority。
- `elab` 负责 one-shot resolution、resolved/core typing 和 lowering，不负责定义新逻辑。
- `parser` 负责文本语法、normalize、桥接和局部环境管理，不得偷偷改变 connector
  语义或 scope 规则。
- `tactics` 负责 goal-state transformation 和 replay orchestration，不拥有 theorem authority。
- `prover` 只是 parser + tactics + kernel 的编排入口；支持子集上可返回可信 `Thm`，
  不支持路径必须继续 fail-closed。
- 当前仓库不再保留旧 phase0/demo `cmd` 路径；当前 `src/cmd` 是 file-first 的
  非权威入口，仍不得成为第二证明内核。

包边界上的 `Thm` 仍然是 opaque type；外部调用者必须通过 checked/stateful 接口交互。

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

`RTerm` 的目的不是替代 kernel term，而是冻结 one-shot resolution 结果。当前
`ResolvedConst` 记录：

- `name`
- `const_id`
- `inst_ty`
- `schema_ty`

这意味着常量在 elaboration 时就被绑定到当时的 kernel identity，后续 `push` /
`pop` / shadowing 只影响未来的名字解析，不会回写既有 resolved object。

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
  - `\not` / `\and` / `\or` / `\imp` 会归一化为规范形式；
  - `|-` 会归一化为 `⊢`；
  - 基础冗余空白会被压缩；
  - 这个阶段不会做 AST 级 pretty print。
- `ParseError.offset` 仍然映射回用户原始输入，而不是归一化后的字符串坐标。
- 规范展示语法以 Unicode 为主：
  - term：`¬`、`∧`、`∨`、`->`、`=`
  - goal：`⊢`
- 兼容输入仍接受：
  - `\not`、`\and`、`\or`、`\imp`
  - `|-`
- 不再接受旧式 ASCII 连接词写法：`/\`、`\/`
- theorem script raw 入口当前支持：
  - theorem header 上零个或多个 `(name : type)` binder
  - 单行 `theorem <name> : <goal> := by <step>; <step>; ...`
  - 块状 `theorem <name> : <goal> := by` 后按换行分隔的顺序 step 列表
- theorem-script AST 当前会为 theorem header binder、theorem goal 与每个 step
  保留 raw-source span；这些位置仍对用户原始输入负责，不会静默改写到
  normalize 后坐标。
- theorem header binder 当前只建立 goal lowering 用的 local parse env；
  它不是 quantifier surface，不会给 tactic/prover 新增 theorem authority。

当前 parser 还公开了：

- `parse_let`
- `parse_def_function`

它们当前是 parser-side utility / experimental surface，已测试但尚未接入主 theorem-script
 产品路径；文档和计划必须诚实地按这个级别描述它们。

### Surface Connectors

`¬` / `->` / `∧` / `∨` 当前都是 surface connector，不是 kernel primitive logic。

统一合同包括：

- parser/bridge 在 lowering 时通过 `logic` 层的 basis-backed builder 生成 proposition term；
- `prop_mk_not` / `prop_mk_imp` / `prop_mk_and` / `prop_mk_or` 对非 `bool` 输入必须返回
  `LogicError`，不能崩溃；
- 这些 connector 的可信语义基础来自 kernel term、equality `=`、choice `@` 与 checked
  primitive rules；
- 它们不能在 `tactics`、`prover` 或未来 `cmd` 中被当成额外的 rule authority；
- parser 不再要求 state 里预先存在普通同名常量，才能解析这些 connector；
- `logic.install_prop_prelude` 只有在当前同名常量已经具备 canonical definition theorem
  时才视为幂等成功；同名同型但非 canonical 的占位常量必须拒绝；
- `prop_dest_not` / `prop_dest_imp` / `prop_dest_and` / `prop_dest_or` 当前采用
  state-backed trusted recognition：只承认 canonical basis term 或当前 state 中具备 canonical
  definition theorem 的 connector 常量。

### Logic Helpers

`src/logic` 当前已经承担未来 theorem replay 扩面的基础工具层，稳定可见能力包括：

- proposition basis term builder：
  - `prop_mk_not`
  - `prop_mk_imp`
  - `prop_mk_and`
  - `prop_mk_or`
- proposition destructor：
  - `prop_dest_not`
  - `prop_dest_imp`
  - `prop_dest_and`
  - `prop_dest_or`
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
- proposition replay helper：
  - `logic_prop_close_hypothesis`
  - `logic_prop_ensure_sequent`
  - `logic_prop_discharge_imp_prefix`
  - `logic_prop_replay_imp_elim_backward`
  - `logic_prop_merge_conjunction`
  - `logic_prop_or_wrap_left`
  - `logic_prop_or_wrap_right`
- theorem catalog / resolver helper：
  - `logic_prop_theorem_count`
  - `logic_prop_theorem_at`
  - `logic_prop_theorem_entry`
  - `logic_prop_resolve_exact_theorem`
  - `logic_prop_resolve_apply_theorem`

这些 helper 的目标是让 future proof synthesis 和 theorem catalog 扩展继续显式 replay
 kernel-checked path，而不是在前端偷偷增加语义捷径。

## Proof Scripting Status

当前 proof scripting 层在**已支持的战术与 prelude 规则**上会通过 `logic` 回放构造内核
 `Thm`；不支持的输入仍 fail-closed，不会伪造定理。

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
- `prove_theorem_script_detailed`
- `prove_theorem_script_with_diagnostics`

当前支持的 step 只有：

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`

当前 `exact` / `apply` 已不再局限于 local-name-only operation。

- `exact` 当前按 witness 语义工作：先解析 local hypothesis witness；若 local miss，
  则解析 exact-capable theorem entry，并要求它能直接 witness 当前 sequent。
- `apply` 先解析 local implication；若 local miss，则可解析一小组稳定命题定理名或上下文派生命题定理。
- 当前 exact-capable theorem names 包括：
  - `imp_refl`
  - `truth`
  - `and_elim_l`
  - `and_elim_r`
  - `and_intro`
  - `not_elim`
  - `ex_falso`
  - `imp_elim`
  - `eq_refl`
  - `eq_sym`
  - `eq_mp`
- 当前 implication-backed apply names 包括：
  - `and_elim_l`
  - `and_elim_r`
  - `or_intro_l`
  - `or_intro_r`
  - `eq_sym`
- `or_intro_l` / `or_intro_r` 当前保持 `apply`-only；它们需要 backward replay
  构造前提，因此不属于当前 goal 的 direct witness。
- 当前 theorem-name inventory 已由 `logic` 统一公开，并由 `tactics`、`prover`、
  tests 与文档共同消费；后续不得再在 `ProofState` 中散落维护另一套 theorem-name
  语义。
- 这些名字都必须 replay 到现有 kernel-checked `Thm`；它们不是新的 proof authority。
- `exact` 不会隐式退化成 `apply`；需要先构造新子目标、再靠 backward replay
  补完的名字，不属于 `exact`。
- local `exact h` 当前只接受 active hypothesis alias；一旦名字命中 local，
  就不会再回退到同名 theorem entry。
- `apply` 只接受 implication theorem；对 `truth` / `not_elim` / `ex_falso` 这类 direct-close
  theorem name 必须诚实失败。

当前语义边界应这样理解：

- `tactics` 负责变换未解目标栈，并组织 replay 所需的证据；
- `prover` 负责解析 script、建立 goal、执行 step；
- `prove_theorem_script_detailed` / `prove_theorem_script_with_diagnostics`
  当前会在诚实失败时保留 theorem 名、step index、当前 goal、local hypotheses、
  以及 goal/step 的 raw-source location；这些诊断对象是工程辅助信息，不是新的 proof object；
- `ps_qed` 仅在 replay 成功且与根目标相继式一致时返回最终 `Thm`；
- `ps_qed` 当前按 strict normalized sequent matching 验证最终 theorem：
  先统一做 proposition beta normalization，再检查假设集合与结论的 alpha-invariant
  一致性；旧的宽 shape match 已不再接受。
- 不支持的路径继续返回 `ProofSynthesisUnavailable`、`Logic` 或 tactic error 等诚实失败。

## Current Support Matrix

### Shipped now

- checked kernel + scoped signature + gate discipline
- resolved elaboration boundary
- parser normalize/raw-offset/theorem-script raw parsing, including sequential
  block bodies、theorem-header binders，以及 raw binder/goal/step spans
- proposition prelude definition theorems + unfold helpers
- supported propositional tactic replay to kernel `Thm`
- file-first `cmd` workflow for single theorem-script files

### Explicitly not shipped

- richer theorem blocks
- quantifier-oriented frontend
- promoted rewrite/simplify tactic or command surface
- holes / metavariables
- dictionary passing / typeclass frontend
- arbitrary theorem-environment references
- arbitrary script completeness

### Active next line

- theorem-reconstruction hardening baseline is now the required gate before
  frontend expansion;
- `M4b`: structured branch blocks for `split` / `left` / `right` beyond the
  current sequential forms

### Stable theorem-name surface

| Surface | Current supported capability | Stable theorem names |
| --- | --- | --- |
| `exact` | local hypothesis witness, theorem entries with exact capability | `imp_refl`, `truth`, `and_elim_l`, `and_elim_r`, `and_intro`, `not_elim`, `ex_falso`, `imp_elim`, `eq_refl`, `eq_sym`, `eq_mp` |
| `apply` | local implication, implication-backed named theorem, implication-backed context theorem | `and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`, `eq_sym` |

稳定合同包括：

- `exact` 只消费 exact capability；不会隐式退化成 `apply`。这既包括
  direct-close entry，也包括 context-derived exact entry；local `exact h`
  也必须把 `h` 解释成当前 sequent 的直接 witness，并且 `h` 必须仍然是 active
  hypothesis alias，而不是 shape-based 猜测或其它 local artifact。
- `apply` 只消费 implication-backed capability；不会把 direct-close theorem
  name 当成 implication 接受。
- wrong-mode theorem usage 继续诚实失败；`exact or_intro_l` 当前返回
  `GoalShapeMismatch`，local `exact h` 若 `h` 不是当前 goal 的直接 witness 也返回
  `GoalShapeMismatch`；`apply truth`、`apply ex_falso`、`apply not_elim`
  当前都必须返回 `ApplyMismatch`。
- local name resolution 仍保持 `local > theorem name`。

### M3c Corpus / Mapping Matrix

当前 shipped subset 的 canonical corpus 采用“双轨”：

- 可执行语料：
  - `src/prover/prover_positive_corpus_test.mbt`
  - `src/prover/prover_negative_corpus_test.mbt`
  - `src/prover/prover_mapping_matrix_test.mbt`
- 可读映射：
  - 本节的支持矩阵与示例来源说明

其中：

- `manual:runnable_examples` 表示当前对外公开的 runnable theorem-script examples；
- `manual:support_matrix` 表示当前公开的支持矩阵正例；
- `manual:failure_matrix` 表示当前公开的 honest failure / negative 示例；
- `internal_only` 表示仍属于 canonical corpus，但当前不直接放进文档正文示例。

| Corpus case | Visibility / anchor | Surface | Catalog / capability | Current contract |
| --- | --- | --- | --- | --- |
| `pos_intro_exact_identity` | `public_example` / `manual:runnable_examples` | `intro` + `exact h` | `local_fact` / `intro_exact` | 局部假设直接闭合 |
| `pos_local_shadow_exact_named_theorem` | `public_example` / `manual:support_matrix` | `exact imp_refl` | `local_fact` / `mixed` | `local > theorem name` |
| `pos_exact_imp_refl` | `public_example` / `manual:support_matrix` | `exact imp_refl` | `direct_close` / `exact_named_direct_close` | direct-close theorem |
| `pos_exact_and_elim_l` | `public_example` / `manual:support_matrix` | `exact and_elim_l` | `context_derived` / `exact_context_derived` | 依赖上下文 conjunction owner |
| `pos_apply_and_elim_l` | `public_example` / `manual:runnable_examples` | `apply and_elim_l` | `implication_backed` / `apply_named_imp` | implication-backed context replay |
| `pos_apply_or_intro_l` | `public_example` / `manual:support_matrix` | `apply or_intro_l` | `implication_backed` / `apply_named_imp` | implication-backed goal-shape replay |
| `pos_split_conjunction` | `public_example` / `manual:support_matrix` | `split` | `structural_only` / `split` | 结构性 goal orchestration |
| `pos_left_disjunction` | `public_example` / `manual:runnable_examples` | `left` | `structural_only` / `left` | 析取目标分支选择 |
| `pos_exact_truth` | `public_example` / `manual:runnable_examples` | `exact truth` | `direct_close` / `exact_named_direct_close` | `T` 目标直接闭合 |
| `pos_exact_ex_falso` | `public_example` / `manual:runnable_examples` | `exact ex_falso` | `context_derived` / `exact_context_derived` | 假设 `F` 时诚实闭合任意 bool 目标 |
| `neg_exact_or_intro_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `exact or_intro_l` | apply-only theorem misuse in exact mode | `GoalShapeMismatch` |
| `neg_apply_truth_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | direct-close theorem misuse | `ApplyMismatch` |
| `neg_local_shadow_truth_is_not_implication` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | local shadow failure | 仍先解析 local，再诚实失败 |
| `neg_exact_context_missing` | `public_failure_example` / `manual:failure_matrix` | `exact and_elim_l` | context-derived missing owner | `GoalShapeMismatch` |
| `neg_non_bool_connector_rejected` | `public_failure_example` / `manual:failure_matrix` | `f ∧ Q` | frontend boundary reject | 非 `bool` connector fail-closed |

### Runnable theorem-script examples

下面这些脚本当前是**真实可运行**的支持子集示例；它们都已有回归测试覆盖，不是规划能力：

```text
theorem t1 : ⊢ P -> P := by intro h; exact h
theorem t2 : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h
theorem t3 : ⊢ P -> P ∨ Q := by intro h; left; exact h
theorem t4 : ⊢ T := by exact truth
theorem t5 : F ⊢ Q := by exact ex_falso
```

这些例子当前由 `src/prover/prover_test.mbt`、`src/prover/prover_positive_corpus_test.mbt`
和 `src/tactics/proof_state_test.mbt` 中的正例回归覆盖；新增或修改对外示例时，应先让
对应测试事实成立，再更新文档。

当前公开 runnable examples 与 canonical case id 的映射是：

| Example | Corpus case | Current support path |
| --- | --- | --- |
| `t1` | `pos_intro_exact_identity` | local fact / `intro_exact` |
| `t2` | `pos_apply_and_elim_l` | implication-backed / `apply_named_imp` |
| `t3` | `pos_left_disjunction` | structural-only / `left` |
| `t4` | `pos_exact_truth` | direct-close / `exact_named_direct_close` |
| `t5` | `pos_exact_ex_falso` | context-derived / `exact_context_derived` |

`src/prover/prover_mapping_matrix_test.mbt` 是当前 corpus case、能力标签与文档锚点之间的
单一测试锚点；若文档要新增、修改或删除公开示例，应先更新对应 canonical case，再同步
更新 mapping matrix 和本文档。

## File-First Workflow

当前 shipped `cmd` 入口是：

```bash
moon run src/cmd <file>
```

当前合同是：

- 输入是单个 theorem-script 文件；
- 成功输出 `ok <theorem_name>: <conclusion_summary>`；
- 失败输出保留 `error[kind]`、文件路径、theorem name，并在 tactic failure 上额外给出：
  - `step`
  - `goal`
  - `locals`

当前可回归的最小例子是：

```text
theorem truth_file : ⊢ T := by exact truth
```

## Current Trajectory

当前外围工程仍应沿着以下方向继续收口：

- 保持 theorem inventory、mode-aware resolver 与 corpus/matrix 的单一来源；
- 先完成 theorem-reconstruction hardening 的 corpus/integration 收口，再推进
  `M4b` structured branch blocks；
- 在不扩大信任边界的前提下，扩展 theorem-script 表达力与更自然的前端诊断；
- 继续让 file-first workflow 复用同一套 corpus / mapping matrix，而不是分叉出第二套语义；
- 让整个可执行前端越来越接近 Part II 所要求的 faithful realization，而不是在
  parser、tactics 或 prover 中引入 ad-hoc proof shortcut。

## Validation Gate

当前贡献者应使用以下门禁核对实现与文档是否一致：

```bash
moon build
moon test
cd formal_verification
lake build
```

若涉及 `.mbti` 变化或准备合并，还应执行：

```bash
moon info
moon fmt
moon test
```

2026-04-05 本地核对结果：

- `moon test` 通过
- `lake build` 通过

需要进一步看论文对齐、代码/测试映射和外围工程 checklist 时，请阅读 `doc/conformance.md`。
