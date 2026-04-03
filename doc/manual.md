# QED Manual

本手册描述 QED 当前 MoonBit 实现线的实际能力、信任边界与用户入口。它参考 Lean 4 参考手册的写法风格，但内容以本仓库当前代码与测试为准。

## 1. About This Manual

本节说明本手册的定位。

QED 目前有三层需要明确区分的信息来源：

- 规范层：[`doc/qed_formal_spec.pdf`](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/qed_formal_spec.pdf) 是规范性来源。
- 实现层：`src/kernel`、`src/elab`、`src/parser`、`src/logic`、`src/tactics`、`src/prover` 构成当前可执行实现。
- 说明层：本手册是实现状态文档，用于说明哪些规范内容已经实现，哪些只是工程扩展，哪些仍未实现。

本手册不替代形式化规范，也不宣称 MoonBit 实现已经被 Lean 4 逐行证明等价。当前“实现正确性”的证据主要来自三部分：

- 导出的公共接口与源码结构；
- 与规范对照的 traceability 文档；
- 当前主干上 `moon test` 全绿，仓库现有测试总数为 161。

当前审计结论如下：

- 论文 Part I 的逻辑核心与 Part II 中面向符合性的工程实现部分，已经在当前 MoonBit 代码库中大体落地。
- 论文中的 `Lawful Axiomatic Type Classes via Dictionary Passing` 章节尚未实现，当前应视为 refinement blueprint，而不是现有能力。
- `elab` 的 resolved boundary 现已按上下文与 frozen constant identity 做 fail-closed 检查；但 `tactics/prover` 仍是 goal-transformation 原型，尚不能从脚本重建一个可信的 kernel theorem。

## 2. Architecture Overview

本节概述 QED 的模块分层与职责。

QED 采用 kernel-first 架构。只有内核构造定理；其余模块只负责构造输入、冻结解析结果或调度内核已检查的规则。

- `src/kernel`
  可信内核。负责类型、项、定理对象、签名状态、primitive rules，以及 definitional/specification/type-definition gate。
- `src/logic`
  对内核 checked 接口的薄封装，并提供命题 prelude。
- `src/elab`
  负责 named term 到 resolved term 的 one-shot elaboration，以及 resolved term 的 core typing 与 lowering。
- `src/parser`
  负责文本语法到 `SynTerm` / `SynGoal` / theorem script 的解析，并桥接到 elaboration 与 kernel term。
- `src/tactics`
 负责 `Goal`、`ProofState` 和当前支持的 tactic step 执行。当前它是 operational goal transformer，而不是 theorem-producing engine。
- `src/prover`
 负责线性 `theorem ... := by ...` 脚本入口。当前它能解析并执行脚本步，但会在最终 theorem synthesis 处 fail-closed。

信任边界应理解为：

- `kernel` 是 theorem construction boundary。
- `logic`、`elab`、`parser`、`tactics`、`prover` 都不是新的逻辑规则层。
- 上层接受用户输入后，最终仍必须落到内核导出的 checked 路径上。

## 3. Trusted Kernel

本节描述当前可信内核已经提供的对象与操作。

### 3.1 Types and Terms

QED 当前实现的核心类型构造包括：

- `bool`
- `ind`
- `fun(a, b)`
- 一般 `TyApp` / type variable 表示

常用构造与观察接口包括：

- `bool_ty`
- `ind_ty`
- `fun_ty`
- `mk_tyvar`
- `mk_tyapp`
- `dest_fun_ty`
- `type_of`
- `to_db_term`
- `from_db_term`

当前实现既保留 named `Term`，也保留 typed De Bruijn `DbTerm`。规则核心在 De Bruijn 层执行，外部 API 则仍以 named `Term` 为主。

### 3.2 Theorem Object and Primitive Rules

QED 对外暴露的是 opaque `Thm`，以及 checked theorem-construction API。

当前已实现并测试的 primitive rule 路径包括：

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

这些规则都经由当前 `KernelState` 做可接受性检查。上层不能绕过 state admissibility 直接伪造定理对象。

### 3.3 Scoped Signatures and Extension Gates

QED 当前实现了带作用域栈的签名状态，而不是“单个全局常量表”。

公共状态接口包括：

- `empty_kernel_state`
- `ks_push_scope`
- `ks_pop_scope`
- `ks_add_const`
- `ks_mk_const`
- `ks_mk_const_instance`
- `ks_define_const`
- `ks_define_const_thm`
- `ks_specify_const`
- `ks_register_type_definition`

这部分对应论文中的几类门禁：

- `DefOK`
- `TypeDefOK`
- `SpecOK`

实现中已经包含：

- definition head monotonicity
- shadowing / pop discipline
- ghost type variable rejection
- definition closure / cycle rejection
- typedef witness validity
- specification witness checks

此外，当前状态还暴露审计辅助接口：

- `ks_extension_cert_count`
- `ks_extension_cert_at`
- `ks_conservative_replay_ok`

这些对象只用于审计与 replay 检查，不是 proof object，也不构成额外的逻辑信任入口。

## 4. Implemented Parts of the Formal Spec

本节给出“论文规范到当前实现”的状态分类。

### 4.1 Implemented and Tested

以下能力已经在当前代码与测试中落地：

| 规范内容 | 当前实现 |
| --- | --- |
| typed type/term core | `src/kernel/types.mbt`、`src/kernel/terms.mbt` |
| named-to-De Bruijn boundary conversion | `to_db_term` / `from_db_term` 与相关 rule core |
| theorem object opacity and checked primitive rules | `src/kernel/thm.mbt` |
| scoped signature stack and shadowing discipline | `src/kernel/sig.mbt` |
| definitional extension gate (`DefOK`) | `ks_define_const*` |
| controlled type-definition / specification extension gates | `ks_register_type_definition`、`ks_specify_const` |
| admissibility checks around `INST_TYPE` | `inst_type` 与 kernel admissibility predicates |
| audit certificates / conservative replay hooks | `ks_extension_cert_*`、`ks_conservative_replay_ok` |
| resolved-term elaboration boundary with frozen constant identity | `src/elab/resolved.mbt` |
| principal-schema instance checking for polymorphic constants | `ks_mk_const_instance`、`ty_is_instance_of`、resolved constant typing |

这些内容都有对应的源码与测试覆盖，且和论文章节可以建立明确映射。

### 4.2 Implemented as Engineering Realization Beyond the Paper Core

以下能力是当前工程实现提供的用户入口。它们依赖内核，但不应被视为“新增 primitive logic”。

- parser syntax
- `let` 声明
- 单参数 `def`
- `Goal`
- `ProofState`
- 线性 `theorem ... := by ...` 的 raw parsing 与 operational execution
- `intro` / `exact` / `apply` / `assumption` / `split` / `left` / `right`

这类功能主要位于：

- `src/parser`
- `src/tactics`
- `src/prover`

它们的角色是把用户语法、局部环境和 proof script 转换成一串 kernel-checked 步骤。

### 4.3 Not Implemented

以下内容当前没有实现，应明确视为缺失能力，而不是“已有但文档未写”：

- dictionary passing
- typeclass resolution / instance search
- constraint solving
- metavariables / holes
- local type inference
- higher-order unification
- richer theorem-script block syntax

其中最需要明确的是：论文中 `Lawful Axiomatic Type Classes via Dictionary Passing` 一节目前仍是 blueprint。当前仓库没有实例环境、字典构造、约束求解或自动字典插入的可执行实现。

## 5. Frontend Elaboration and Parser

本节描述当前前端 elaboration 与 parser 已经支持的行为。

### 5.1 Resolved Elaboration Boundary

QED 当前前端保留三层项表示：

- named `Term`
- resolved `RTerm`
- typed De Bruijn `DbTerm`

其中 `RTerm` 的作用是冻结 one-shot resolution 结果。当前 `ResolvedConst` 记录：

- `name`
- `const_id`
- `inst_ty`
- `schema_ty`

这意味着常量解析完成后，后续作用域变化不会把旧对象重新绑定到一个同名但不同身份的常量上。

当前公共 elaboration 接口包括：

- `elab_resolve_name`
- `elab_resolve_const_by_name`
- `elab_resolve_const_instance`
- `elab_resolve_named_term`
- `elab_core_type_of`
- `elab_lower_to_term`
- `elab_lower_to_db`

这里的 core typing 是对 resolved term 的独立检查，不依赖重新跑 parser。

### 5.2 Parser Surface Syntax

当前 parser 支持的 term 语法包括：

- 名称：`P`、`f`
- 应用：`f x`、`f x y`
- 前缀否定：`¬ t`、`\not t`
- 中缀：`=`、`∧`、`∨`、`->`
- 括号：`(f x) = y`

当前 goal 语法包括：

- `H1, H2 |- C`
- `H1, H2 ⊢ C`
- `|- C`
- `⊢ C`

当前 theorem script raw 语法包括：

```text
theorem <name> : <goal> := by <step>; <step>; ...
```

当前 `step` 仅支持：

- `intro n`
- `exact n`
- `apply n`
- `assumption`
- `split`
- `left`
- `right`

当前 parser 公共入口包括：

- `parse_term_raw`
- `parse_goal_raw`
- `parse_theorem_script_raw`
- `parse_term`
- `parse_goal`
- `parse_resolved_term_with_env`
- `parse_goal_with_env`
- `parse_let`
- `parse_def_function`

需要注意的是，`parse_theorem_script_raw` 属于 parser 层的语法能力；它不意味着当前 prover 已经可以把脚本闭合为最终定理。

### 5.3 Local Environment and Lowering

当前 parser 的本地环境是 `ParseEnv`，并使用 `local > const` 的名称解析顺序。

示例：

```text
let x : A
```

这会把后续文本中的 `x` 降到局部自由变量，而不是去全局常量表中重查同名符号。

单参数定义目前支持：

```text
def id(x : A) : A { x }
```

底层路径是：parser 解析文本，elaboration 生成项，再调用 `ks_define_const_thm` 走 definition gate。

### 5.4 Current Limitations

前端当前限制如下：

- 不支持 `lambda` 文本语法。
- 不支持 `forall` / `exists` 文本语法。
- 不支持多参数或模式匹配 `def`。
- `exact` 与 `apply` 当前只接受名称，不接受任意 term。
- 不支持洞、mvar、局部类型推断或自动约束求解。

## 6. Proof Scripting Layer

本节描述当前 proof scripting 的执行模型。

QED 当前提供的是一个小型、线性的 proof scripting 层，而不是完整交互式 tactic framework。它目前只能做 goal-state 变换，不能把脚本最终综合为可信的 kernel theorem。

### 6.1 Goal and ProofState

目标对象是：

- `Goal { hyps : Array[Term], concl : Term }`

证明状态对象是：

- `ProofState`

常用接口包括：

- `mk_goal`
- `ps_init`
- `ps_current_goal`
- `ps_goal_count`
- `ps_apply`
- `ps_apply_script`
- `ps_qed`

### 6.2 Supported Tactic Steps

当前支持七个 step：

- `step_intro`
- `step_exact`
- `step_apply`
- `step_assumption`
- `step_split`
- `step_left`
- `step_right`

它们分别对应：

- 引入蕴含前件或局部假设
- 用已有名称直接闭合当前目标
- 通过规则名或局部名字展开子目标
- 在当前假设中寻找可直接闭合的目标
- 拆分合取目标
- 选择析取左支
- 选择析取右支

当前脚本执行始终处理 DFS 顺序下的第一个未解目标。

### 6.3 Prover Entry

`src/prover` 当前对外暴露：

- `default_prover_options`
- `prover_options`
- `prove_theorem_script`

其中 `default_prover_options()` 默认会自动安装命题 prelude，因此 `->`、`¬`、`∧`、`∨` 这些语法在 prover 入口中通常可以直接使用。

需要注意的是，prover 只是 parser + tactics + kernel 的编排层。它本身不引入新规则。

当前状态下，`prove_theorem_script` 会在“脚本步执行完成但需要综合最终 theorem”时 fail-closed，并返回 tactic 错误，而不是伪造一个看似成功的 `Thm`。这是刻意保守的行为：在连接词只以 prelude 常量存在、而尚未提供相应 derived-rule theorem replay 的前提下，系统不能诚实地产出最终定理对象。

## 7. What Is Not Implemented

本节集中说明当前缺失能力，避免把蓝图内容误认为现状。

### 7.1 Dictionary Passing and Type Classes

当前没有实现：

- instance environment
- class declaration frontend
- instance search
- 自动字典参数插入
- 约束求解与 superclass propagation

因此，论文中关于 lawful axiomatic type classes 的章节应理解为未来 refinement 方向，而不是当前系统行为说明。

### 7.2 Advanced Elaboration

当前没有实现：

- metavariables
- holes
- 局部类型推断
- 高阶统一
- 基于约束的 elaboration

现有 elaboration 是 one-shot、显式、非约束驱动的。

### 7.3 Richer Proof Language

当前没有实现：

- 分支 proof block
- `rw` / `simp` 风格 tactic
- 更复杂的 tactic 组合子
- 接受任意 term 参数的 `exact` / `apply`
- 从 `ProofState` / theorem script 到最终 kernel `Thm` 的完备证明重建

当前 theorem script 应被理解为一个最小线性脚本语言。

## 8. Examples

本节给出当前实现确实支持的小示例。

### 8.1 Kernel-Level Example

下面的示例直接使用 kernel state 注册命题常量，并调用 prover 入口执行脚本。当前示例展示的是 fail-closed 行为，而不是成功产出 theorem。

```moonbit
///|
using @kernel {bool_ty, empty_kernel_state, ks_add_const}

///|
using @prover {default_prover_options, prove_theorem_script}

///|
fn[T, E] expect_ok(res : Result[T, E]) -> T {
  match res {
    Ok(v) => v
    Err(_) => panic()
  }
}

///|
test "manual demo: theorem-by is parsed and executed, but theorem synthesis is unavailable" {
  let st0 = expect_ok(ks_add_const(empty_kernel_state(), "P", bool_ty()))
  let src = "theorem t1 : ⊢ P -> P := by intro h; exact h"
  assert_true(
    prove_theorem_script(st0, src, default_prover_options())
    is Err(Tactic(ProofSynthesisUnavailable(_))),
  )
}
```

这个示例说明：

- theorem script 由 `prover` 解析与执行；
- prelude 中的 `imp` 会在 prover 入口按选项自动安装；
- 当前系统不会把这个脚本伪装成一个已经构造完成的 kernel theorem。

### 8.2 Parser Environment Example

下面的文本声明当前是支持的：

```text
let x : A
def id(y : A) : A { y }
```

第一行向 `ParseEnv` 加入局部自由变量。第二行定义一个单参数常量，其函数体会被 lower 为带 binder 的项，并接受 definition gate 检查。

### 8.3 ProofState Example

若目标是 `⊢ P -> P`，当前标准执行路径是：

1. `ps_init` 创建初始 `ProofState`
2. `intro h` 把前件引入局部上下文
3. `exact h` 用局部名称闭合目标
4. `ps_qed` 在无未解目标时，当前会返回 `ProofSynthesisUnavailable`

这说明当前 tactic 层是一层状态机式脚本执行器，而不是可任意扩展的元编程系统，也还不是一个 theorem-producing proof engine。

## 9. Reference Map

本节列出进一步查阅时最重要的文件。

### 9.1 Normative and Audit Documents

- [`doc/qed_formal_spec.pdf`](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/qed_formal_spec.pdf)
- [`doc/kernel_paper_traceability.md`](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/kernel_paper_traceability.md)
- [`doc/elab_boundary.md`](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/elab_boundary.md)
- [`doc/parser_v0.md`](/Users/kcn/Desktop/repos/MoonVibe/QED/doc/parser_v0.md)

### 9.2 Public API Surfaces

- [`src/kernel/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/kernel/pkg.generated.mbti)
- [`src/elab/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/elab/pkg.generated.mbti)
- [`src/parser/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/parser/pkg.generated.mbti)
- [`src/logic/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/logic/pkg.generated.mbti)
- [`src/tactics/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/tactics/pkg.generated.mbti)
- [`src/prover/pkg.generated.mbti`](/Users/kcn/Desktop/repos/MoonVibe/QED/src/prover/pkg.generated.mbti)

### 9.3 Validation Baseline

当前手册所依据的最小验证基线是：

```bash
moon test
```

在本次核对中，该命令通过，测试总数为 163。
