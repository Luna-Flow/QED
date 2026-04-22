# QED Manual

Status: active
Audience: users, contributors, implementers
Authority: user guide + implementation contract; subordinate to `doc/qed_formal_spec.pdf` and current code/tests
Scope: current shipped behavior, beginner-facing usage, trust boundary, support matrix, and stable examples
Last reviewed: 2026-04-20

本文档既是 QED 当前的用户手册，也是实现合同。

它以当前仓库工作区中的 MoonBit 与 Lean 代码为准，用来回答三件事：

- 普通用户现在怎样实际写出和运行一个小证明；
- 现在真正实现了什么；
- 外围工程当前被允许做什么、不能做什么。

## 先给第一次接触 HOL 的读者

如果你以前没有接触过 HOL、Lean、HOL Light、Isabelle 这类证明助手，可以先用下面这组直觉理解 QED 当前 shipped 的子集：

- 这里的“证明”不是自然语言段落，而是一段会被内核检查的 script。
- 当前 shipped 的目标主要是最小命题逻辑子集，加上一小部分等式与 theorem replay。
- `⊢ goal` 表示“在空前提下证明 `goal`”。
- `A, B ⊢ goal` 表示“在假设 `A` 和 `B` 的前提下证明 `goal`”。
- `T` 可以先直觉地理解成“永真命题”，`F` 理解成“假命题”。
- `A -> B` 表示“如果有 `A`，就可以推出 `B`”。
- `A ∧ B` 表示“同时证明 `A` 和 `B`”。
- `A ∨ B` 表示“证明 `A` 或 `B` 中的一边即可，但要明确选左边还是右边”。
- `P = Q` 表示等式；当前 shipped 子集里也支持少量等式相关 theorem replay。

当前 theorem script 可以先粗略理解成“面向目标的证明步骤”：

- `intro h`：如果当前目标是 `A -> B`，就把它变成“新增一个叫 `h` 的局部假设 `A`，继续证明 `B`”。
- `exact h`：如果 `h` 已经是当前目标的直接证据，就立刻闭合。
- `assumption`：在当前局部假设里找与目标匹配的证据。
- `apply th`：把某个蕴含型 theorem 或局部蕴含假设用于当前目标，产生新的子目标。
- `split`：当目标是 `A ∧ B` 时，拆成两个子目标。
- `left` / `right`：当目标是 `A ∨ B` 时，显式选择证明左支或右支。
- `hole`：承认这里还没证明完，系统会返回结构化 unfinished 结果，而不是伪造成功。

这份直觉足够支撑你开始读用户手册里的前几个例子；更完整的边界、规则名称和支持矩阵见后文。

## 上手顺序

建议按下面顺序开始：

1. 先跑 `moon build` 和 `moon test`，确认工作区本身是绿的。
2. 用 `src/cmd` 跑一个完全 state-free 的定理文件，先熟悉输入输出格式。
3. 再尝试带 theorem-header binder 的例子，理解“局部变量如何进入证明上下文”。
4. 最后再看支持矩阵、failure matrix 和实现合同，理解哪些能力是 shipped，哪些还没有。

## 快速开始

### 1. 构建

```bash
moon build
moon test
```

### 2. 跑第一个证明文件

在仓库根目录创建一个文件，例如 `truth_file.qed`：

```text
theorem truth_file : ⊢ T := by exact truth
```

然后执行：

```bash
moon run src/cmd truth_file.qed
```

当前成功输出形如：

```text
ok truth_file
```

如果需要查看完整 conclusion summary，可加 `-d`：

```bash
moon run src/cmd -- -d truth_file.qed
```

通过 `moon run` 启动时，`--` 是 MoonBit runner 的参数分隔符；没有它，
`-d` 会先被 `moon` 解析，QED CLI 收不到这个开关。编译成独立可执行文件后，
可以直接写：

```bash
qed-cmd -d truth_file.qed
```

包含 `hole` 的 theorem 会作为 `warning[unfinished]` 输出；它不会构造 theorem，
也不会进入后续 kernel state。默认 warning 会让整体退出码为非 0；如果只想在没有
真正 error 时允许 warning，可以使用 `--no-warn`：

```bash
moon run src/cmd -- --no-warn file.qed
qed-cmd --no-warn file.qed
```

这个例子适合第一步上手，因为它不依赖额外自由常量，也不要求你提前理解 binder、分支或 theorem inventory。

### 3. 第二个例子：最小的“假设后原样返回”

```text
theorem id_bool (x : bool) : ⊢ x -> x := by
  intro h
  exact h
```

这里有两层要点：

- `(x : bool)` 是 theorem header binder。它把一个局部变量 `x` 引入 theorem goal。
- `intro h` 把目标 `x -> x` 变成“假设 `h : x`，证明 `x`”。
- `exact h` 说明此时局部假设 `h` 就是当前目标的直接证据。

这也是当前最适合没有 HOL 基础的读者理解的脚本：它只展示“目标改写”和“证据闭合”，不依赖额外 theorem name。

### 4. 第三个例子：构造一个合取

```text
theorem dup_bool (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
```

这个例子说明：

- 目标 `x ∧ x` 需要分别证明左右两边；
- `split` 会生成两个分支；
- 每个分支里都可以继续用 `exact h` 闭合。

如果你更喜欢顺序写法，当前也支持先 `split`，再按顺序完成两个子目标；但对初学者来说，`split { ... } { ... }` 的结构化分支块更直观。

### 5. 第四个例子：一个经典的合取交换定理

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
```

这个脚本展示了一个最经典的命题逻辑模式：从 `p ∧ q` 反过来构造 `q ∧ p`。
它比 `x -> x` 更像真正的数学命题，但仍然完全落在当前 shipped 的语法和能力内。

### 6. 第五个例子：看到 honest failure

下面这个脚本是刻意写错的：

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
```

它不会返回 theorem success，而会返回结构化失败。原因是：当前左支目标实际上是 `x`，但 `truth` 只能直接闭合 `T`。

当前 canonical 输出示例见本文后面的 `manual:quantifier_failure_matrix`。

### 7. 第六个例子：看到 unfinished proof

```text
theorem unfinished_branch (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by
  intro h
  right { right { hole h1 } }
```

这里 `hole h1` 表示“我知道还差一个证明点，但现在先留空”。QED 会诚实地返回 unfinished 结果，并保留：

- theorem 名；
- step 序号；
- branch 路径；
- 当前 goal；
- 当前 locals；
- hole 名。

这对于交互式前端、IDE 诊断和后续 proof authoring 很重要，但它不是 theorem。

## 用户视角下的当前输入模型

如果你现在主要是想查“命令行到底接受什么语法”，优先看 `doc/syntax.md`。
本节保留的是更简短的输入模型摘要；支持矩阵、失败语义和实现合同仍以本文为准。

### theorem script 长什么样

当前 shipped 的 theorem script 形状是：

```text
theorem <name> [(binder...)] : <goal> := by <steps>
```

其中：

- `<name>` 是 theorem 名。
- `[(binder...)]` 当前支持零个或多个 `(x : bool)` 这种 theorem-header binder。
- `<goal>` 是一个 sequent，例如 `⊢ T`、`P ⊢ P`、`⊢ x -> x ∧ x`。
- `<steps>` 可以是单行顺序写法，也可以是换行块状写法，还可以在 `split` / `left` / `right` 后接最小结构化 branch block；这类 branch 语法由 parser 接受、由 prover 编排执行。

### 当前最需要知道的限制

如果你是第一次使用 `src/cmd`，下面这几条最重要：

- 直接 file-first 跑脚本时，最好先用 `T`、`F` 和 theorem-header binder `(x : bool)` 这类 state-free 例子。
- 文档里的 `P`、`Q` 这类例子很多是为了说明支持矩阵；它们在测试里会先放进对应的 kernel state，再调用 prover。
- theorem-header binder 已经是 shipped surface；原始 `forall (x : A), body` / `∀ (x : A), body` 现在作为 goal-only sugar 被接受，但仍不是 term-level syntax。
- 当前支持的 step 只有 `intro`、`exact`、`apply`、`assumption`、`split`、`left`、`right`、`hole`。
- 不支持的路径会 fail-closed，不会伪造 theorem success。

### 命令行工作流

当前 shipped `cmd` 入口是：

```bash
moon run src/cmd <file>
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

输入是 theorem-script 文件；单 theorem 文件可省略末尾 `qed`，多 theorem 文件用
小写 `qed` 分隔。输出有三类：

- 成功：默认每个 theorem 输出一行 `ok <theorem_name>`；使用 `-d` 时输出
  `ok <theorem_name>: <conclusion_summary>`
- 失败：`error[kind] ...`，必要时带 `step`、`branch`、`goal`、`locals`
- 未完成：`warning[unfinished] ...`，并带 `hole`、`goal`、`locals` 等上下文；
  不产生 theorem authority，但会继续检查后续 theorem

`moon run` 下传 `-d` / `--no-warn` 需要 `--` 分隔；独立可执行文件可直接使用
`qed-cmd -d --no-warn <file>`。

这意味着它已经不是“只有成功/失败两类”的黑箱 CLI，而是能把当前 proof state 相关的关键诊断暴露出来。

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
- `parser` 负责文本语法、normalize、parser-owned lowering result 与局部环境管理，
  不得偷偷改变 connector 语义或 scope 规则，也不得直接拥有 tactics execution object。
- `tactics` 负责 goal-state transformation 和 replay orchestration，不拥有 theorem authority，也不解释 theorem-script 的 structured branch 语法。
- `prover` 只是 parser + tactics + kernel 的编排入口；支持子集上可返回可信 `Thm`，
  不支持路径必须继续 fail-closed；它可以显式把 parser lowering result bridge 到
  `tactics.Goal`，并负责 structured branch block 的脚本调度，但不反向把 tactics 对象推回 parser。
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

当前 parser 是“文本语法 -> AST -> resolved elaboration -> parser-owned lowered object”的统一入口。

稳定合同包括：

- 名称解析顺序始终是 `local > const`。
- `parse_goal` / `lower_syn_goal_with_env` 当前返回 parser-owned `ParsedGoal`；
  tactics 执行对象只在上层 bridge 时构造。
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
  - `hole` / `hole <name>` unfinished-proof step
- theorem-script AST 当前会为 theorem header binder、theorem goal 与每个 step
  保留 raw-source span；这些位置仍对用户原始输入负责，不会静默改写到
  normalize 后坐标。
- theorem header binder 当前是已 shipped 的 quantifier-facing surface：
  它会把 binder 名引入 goal lowering、proof-state locals 与 cmd diagnostics；
  但它不会给 tactic/prover 新增 theorem authority。
- `forall (x : A), body` / `∀ (x : A), body` 当前作为 goal-only sugar 被接受；
  但它仍然不是 term-level syntax。

当前 parser 还公开了：

- `parse_let`
- `parse_def_function`

它们当前是已支持的 parser-side utility surface：有测试覆盖、可单独调用，
负责局部环境扩展与闭包式函数定义解析；但它们不是 theorem-script 主语法，
也不会扩展 theorem-construction authority。

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

这些 helper 的目标是让 proof synthesis 和 theorem catalog 的 replay 路径继续保持
显式的 kernel-checked path，而不是在前端偷偷增加语义捷径。

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
- `hole`

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
  branch path，以及 goal/step 的 raw-source location；这些诊断对象是工程辅助信息，不是新的 proof object；
- theorem script 中若出现 `hole`，当前返回结构化 unfinished-proof 结果，
  保留 theorem 名、step index、当前 goal、local hypotheses、branch path、
  hole name 与源码位置；unfinished-proof 结果不是 theorem；
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
  block bodies、structured branch blocks、theorem-header binders、hole step，
  以及 raw binder/goal/step spans
- theorem-header binder 驱动的 quantifier-facing script surface，以及对应的
  prover/cmd goal、locals、branch、unfinished-proof 摘要
- parser-side utility APIs `parse_let` / `parse_def_function`
- proposition prelude definition theorems + unfold helpers
- supported propositional tactic replay to kernel `Thm`
- unfinished-proof reporting for theorem scripts containing holes
- file-first `cmd` workflow for theorem-script files with optional `qed`
  terminators and multiple theorem blocks

### Explicitly not shipped

- richer theorem blocks
- promoted rewrite/simplify tactic or command surface
- kernel metavariables / hole completion authority
- dictionary passing / typeclass frontend
- arbitrary theorem-environment references
- arbitrary script completeness

### Current Extension Contract

- theorem-name inventory、corpus、mapping matrix 与 docs 使用同一组 shipped anchors；
- nested proof blocks 继续通过当前 checked replay boundary 组织；
- hole / unfinished-proof 继续是 frontend contract，不是 kernel metavariable authority；
- theorem-header binder 继续作为当前 shipped quantifier-facing 语法的一部分，并保持与 corpus / matrix 同步；
- 新增公开示例时，必须先进入回归测试，再进入文档锚点。

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

当前 shipped subset 的 canonical corpus 采用“四类”：

- 可执行语料：
  - `src/prover/prover_positive_corpus_test.mbt`
  - `src/prover/prover_negative_corpus_test.mbt`
  - `src/prover/prover_test.mbt` / `src/cmd/cmd_corpus_wbtest.mbt` 中的
    canonical unfinished-proof 回归
  - `src/prover/corpus.mbt` 中的 quantifier-facing binder / raw-`forall`
    canonical cases，
    由 `src/cmd/cmd_corpus_wbtest.mbt` 与
    `src/prover/prover_mapping_matrix_test.mbt` 共同锚定
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
| `pos_split_conjunction` | `public_example` / `manual:support_matrix` | `split` | `structural_only` / `split` | 顺序结构性 goal orchestration |
| `pos_branch_split_conjunction` | `public_example` / `manual:support_matrix` | `split { ... } { ... }` | `structural_only` / `split` | 结构化 conjunction 分支块 |
| `pos_left_disjunction` | `public_example` / `manual:runnable_examples` | `left` | `structural_only` / `left` | 顺序析取目标分支选择 |
| `pos_branch_left_disjunction` | `public_example` / `manual:runnable_examples` | `left { ... }` | `structural_only` / `left` | 结构化析取分支块 |
| `pos_exact_truth` | `public_example` / `manual:runnable_examples` | `exact truth` | `direct_close` / `exact_named_direct_close` | `T` 目标直接闭合 |
| `pos_exact_ex_falso` | `public_example` / `manual:runnable_examples` | `exact ex_falso` | `context_derived` / `exact_context_derived` | 假设 `F` 时诚实闭合任意 bool 目标 |
| `pos_quant_seq_identity` | `public_example` / `manual:quantifier_examples` | `(x : bool)` binder + `intro` / `exact` | `quantifier_surface` / `quantifier_intro_exact` | theorem-header binder 驱动的顺序量词面 |
| `pos_quant_branch_split` | `public_example` / `manual:quantifier_examples` | `(x : bool)` binder + `split { ... } { ... }` | `quantifier_surface` / `quantifier_split_branch` | binder + branch block 的兼容正例 |
| `pos_quant_forall_seq_identity` | `public_example` / `manual:quantifier_examples` | `forall (x : bool), ...` + `intro` / `exact` | `quantifier_surface` / `quantifier_forall_intro_exact` | raw theorem-goal sugar 驱动的顺序量词面 |
| `pos_quant_forall_branch_split` | `public_example` / `manual:quantifier_examples` | `forall (x : bool), ...` + `split { ... } { ... }` | `quantifier_surface` / `quantifier_forall_split_branch` | raw theorem-goal sugar 与 branch block 的兼容正例 |
| `neg_exact_or_intro_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `exact or_intro_l` | apply-only theorem misuse in exact mode | `GoalShapeMismatch` |
| `neg_apply_truth_wrong_mode` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | direct-close theorem misuse | `ApplyMismatch` |
| `neg_local_shadow_truth_is_not_implication` | `public_failure_example` / `manual:failure_matrix` | `apply truth` | local shadow failure | 仍先解析 local，再诚实失败 |
| `neg_exact_context_missing` | `public_failure_example` / `manual:failure_matrix` | `exact and_elim_l` | context-derived missing owner | `GoalShapeMismatch` |
| `neg_non_bool_connector_rejected` | `public_failure_example` / `manual:failure_matrix` | `f ∧ Q` | frontend boundary reject | 非 `bool` connector fail-closed |
| `neg_quant_branch_goal_mismatch` | `public_failure_example` / `manual:quantifier_failure_matrix` | `(x : bool)` binder + `left { exact truth }` | `quantifier_surface` / `quantifier_goal_shape_mismatch` | binder locals 保留且 branch blame 稳定 |
| `neg_quant_forall_branch_goal_mismatch` | `public_failure_example` / `manual:quantifier_failure_matrix` | `forall (x : bool), ...` + `left { exact truth }` | `quantifier_surface` / `quantifier_forall_goal_shape_mismatch` | raw theorem-goal sugar 下的 locals 与 branch blame 稳定 |
| `unf_quant_nested_branch_hole` | `public_example` / `manual:quantifier_unfinished_examples` | `(x : bool)` binder + nested `hole` | `unfinished_proof` / `quantifier_unfinished_hole` | binder locals、nested branch path 与 unfinished rendering |
| `unf_quant_forall_nested_branch_hole` | `public_example` / `manual:quantifier_unfinished_examples` | `forall (x : bool), ...` + nested `hole` | `unfinished_proof` / `quantifier_forall_unfinished_hole` | raw theorem-goal sugar 下的 locals、nested branch path 与 unfinished rendering |

### Runnable theorem-script examples

下面这些脚本当前都是**真实存在于回归语料中的 theorem-script 示例**，不是规划能力。

但要区分两件事：

- “在测试/预置 state 中可运行”；
- “用户直接通过 `moon run src/cmd <file>` 即可运行”。

如果需要查看成功 theorem 的完整 conclusion summary，通过 `moon run` 时使用
`moon run src/cmd -- -d <file>`；编译成独立可执行文件后使用
`qed-cmd -d <file>`。

其中只有不依赖额外自由常量的 state-free 脚本，才适合作为第一次上手的 file-first 示例。对第一次使用本项目的用户，优先看本手册前面的 `truth_file`、`id_bool`、`dup_bool`。

下面这组例子主要用于公开说明当前 shipped theorem-script 子集的覆盖面：

```text
theorem t1 : ⊢ P -> P := by intro h; exact h
theorem t2 : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h
theorem t3 : ⊢ P -> P ∨ Q := by intro h; left; exact h
theorem t4 : P ⊢ P ∨ Q := by left { assumption }
theorem t5 : ⊢ T := by exact truth
theorem t6 : F ⊢ Q := by exact ex_falso
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
| `t4` | `pos_branch_left_disjunction` | structural-only / `left` structured branch |
| `t5` | `pos_exact_truth` | direct-close / `exact_named_direct_close` |
| `t6` | `pos_exact_ex_falso` | context-derived / `exact_context_derived` |

`src/prover/prover_mapping_matrix_test.mbt` 是当前 corpus case、能力标签与文档锚点之间的
单一测试锚点；若文档要新增、修改或删除公开示例，应先更新对应 canonical case，再同步
更新 mapping matrix 和本文档。

### Quantifier-Facing Examples

当前已 shipped 的量词面包含两条用户路径：theorem-header binder 与 raw `forall`
theorem goal sugar。下面这两组脚本当前都已有回归测试与 mapping matrix 锚定：

```text
theorem q1 (x : bool) : ⊢ x -> x := by intro h; exact h
theorem q2 (x : bool) : ⊢ x -> x ∧ x := by intro h; split { exact h } { exact h }
theorem qbad (x : bool) : ⊢ x -> x ∨ x := by intro h; left { exact truth }
theorem qunf (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

```text
theorem qf1 : ⊢ forall (x : bool), x -> x := by intro h; exact h
theorem qf2 : ⊢ forall (x : bool), x -> x ∧ x := by intro h; split { exact h } { exact h }
theorem qfbad : ⊢ forall (x : bool), x -> x ∨ x := by intro h; left { exact truth }
theorem qfunf : ⊢ forall (x : bool), x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

这些例子与 canonical case id 的映射是：

| Example | Corpus case | Current support path |
| --- | --- | --- |
| `q1` | `pos_quant_seq_identity` | quantifier surface / `quantifier_intro_exact` |
| `q2` | `pos_quant_branch_split` | quantifier surface / `quantifier_split_branch` |
| `qbad` | `neg_quant_branch_goal_mismatch` | quantifier failure / `quantifier_goal_shape_mismatch` |
| `qunf` | `unf_quant_nested_branch_hole` | quantifier unfinished / `quantifier_unfinished_hole` |
| `qf1` | `pos_quant_forall_seq_identity` | quantifier surface / `quantifier_forall_intro_exact` |
| `qf2` | `pos_quant_forall_branch_split` | quantifier surface / `quantifier_forall_split_branch` |
| `qfbad` | `neg_quant_forall_branch_goal_mismatch` | quantifier failure / `quantifier_forall_goal_shape_mismatch` |
| `qfunf` | `unf_quant_forall_nested_branch_hole` | quantifier unfinished / `quantifier_forall_unfinished_hole` |

另外，`⊢ (forall (x : bool), x -> x)` 这类带外层括号的写法当前也被 parser /
prover 接受；它沿用同一条 raw-goal-sugar lowering path，只是当前不单独占用
corpus case id。

对没有 HOL 基础的读者，可以把这些量词例子先理解成：

- theorem 里可以先声明一个局部变量，比如 `(x : bool)`；
- 后面的目标里就可以直接引用这个变量；
- raw `forall` theorem goal 当前会 lowering 到同一条 binder-oriented replay path。

当前 shipped 的量词前端包含 binder 入口和 raw `forall` goal sugar；term 位置仍不接受 raw `forall`。
这意味着用户现在已经可以写出并证明 `forall` theorem goal，但它仍然不是通用
term-level quantifier syntax，也没有新增 kernel primitive quantifier authority。

### Unfinished-proof Example

当前 canonical unfinished-proof case 也是回归锚点，不会返回 theorem：

```text
theorem unf_hole_intro : ⊢ T -> T := by intro h; hole h1
theorem unf_nested_branch_hole : ⊢ T ∨ (T ∨ T) := by right { right { hole h1 } }
```

这两个样例当前由 `src/prover/prover_test.mbt`、`src/prover/prover_mapping_matrix_test.mbt`
和 `src/cmd/cmd_corpus_wbtest.mbt` 共同锚定；前者固定 root-level unfinished contract，
后者固定 nested branch path 与 unfinished rendering。

当前 quantifier-facing unfinished 锚点包括 binder 和 raw `forall` 两条路径：

```text
theorem unf_quant_nested_branch_hole (x : bool) : ⊢ x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
theorem unf_quant_forall_nested_branch_hole : ⊢ forall (x : bool), x -> x ∨ (x ∨ x) := by intro h; right { right { hole h1 } }
```

它们当前分别固定 binder / raw-goal-sugar locals、nested branch path 与 CLI unfinished rendering。

## File-First Workflow

当前 shipped `cmd` 入口是：

```bash
moon run src/cmd <file>
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

当前合同是：

- 输入是 theorem-script 文件；单 theorem 文件可省略末尾 `qed`，多 theorem 文件用
  小写 `qed` 分隔；
- 成功输出默认是每个 theorem 一行 `ok <theorem_name>`；使用 `-d` 时输出
  `ok <theorem_name>: <conclusion_summary>`；
- 失败输出保留 `error[kind]`、文件路径、theorem name，并在 tactic failure 上额外给出：
  - `step`
  - `branch`
  - `goal`
  - `locals`
- 若脚本包含 `hole`，当前输出 `warning[unfinished] ...`，并给出 `step`、`branch`、
  `goal`、`locals`、`hole`、`message` 摘要；空值标记稳定为 `<none>` / `<root>`。
  warning 不构造 theorem，但文件级 runner 会继续检查后续 theorem；
- `--no-warn` 只影响 warning-only 文件的退出码，不隐藏 warning 输出；
- `moon run` 下的 `--` 只是把后续参数转发给 QED CLI；编译成独立可执行文件后，
  使用 `qed-cmd -d --no-warn <file>` 即可，不需要 `--`。
- theorem-header binder 脚本与 raw `forall` theorem-goal 脚本沿用同一份 CLI
  合同；`goal` / `locals` 摘要当前固定为 kernel-term string，branch/step blame 与
  unfinished rendering 由 `src/cmd/cmd_corpus_wbtest.mbt` 与
  `src/cmd/cmd_wbtest.mbt` 共同锚定

当前可回归的最小例子是：

```text
theorem truth_file : ⊢ T := by exact truth
```

如果你只是想确认环境和命令链路正常，先跑这个最合适。

对 raw `forall` theorem-goal 文件，当前 canonical CLI 输出示例是：

```text
error[tactic] quant_forall_fail.qed (quant_forall_bad): GoalShapeMismatch(exact theorem does not directly close current goal)
step: 3
branch: 1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
```

```text
warning[unfinished] quant_forall_unfinished.qed (quant_forall_hole): proof contains an unfinished hole
theorem: quant_forall_hole
step: 4
branch: 1.1
goal: [Var(x : bool)] |- Var(x : bool)
locals: h: Var(x : bool)
hole: h1
message: proof contains an unfinished hole
```

theorem-header binder 语法当前使用同一组字段与同一类 blame 口径；对应 canonical
corpus 锚点见 `src/cmd/cmd_corpus_wbtest.mbt`。

## Current Extension Contract

当前可执行前端只允许沿着同一套 shipped anchors 扩展：

- theorem inventory、mode-aware resolver、corpus、mapping matrix 与 docs 保持单一来源；
- structured branch block 作为 prover-side 脚本合同，继续复用现有 checked replay boundary；
- hole / unfinished proof 继续保持 frontend-only contract，不进入 kernel metavariable authority；
- theorem-header binder 继续作为当前 shipped quantifier-facing 用户语法的一部分；
- raw `forall` theorem goal 作为 goal-only sugar 继续保持已支持，不得写成 term-level syntax；
- file-first workflow 继续复用同一套 corpus / mapping matrix，不分叉第二套语义。

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
