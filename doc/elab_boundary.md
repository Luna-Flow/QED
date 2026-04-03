# Resolved Elaboration Boundary

本文档记录 QED 运行时中“named elaboration -> resolved term -> boundary lowering”的实现约定。

对应论文位置：

- `doc/qed_formal_spec.typ` 中的 `Resolution Boundary`
- `Named Elaboration Judgment`
- `Core Typing over Resolved Terms`

## 1. 三层对象

当前实现保留三层项表示：

1. named `Term`
2. resolved `RTerm`
3. typed De Bruijn `DbTerm`

角色分工：

- `Term`：对外接口和现有 tactic/kernel 上层桥接使用。
- `RTerm`：前端 one-shot resolution 的冻结边界。
- `DbTerm`：kernel 内部 alpha-invariant/core-sensitive 计算使用。

## 2. `RTerm` 设计

`RTerm` 位于 `src/elab/resolved.mbt`，构造子为：

- `RVar(name, ty)`
- `RConst(ResolvedConst)`
- `RComb(f, x)`
- `RAbs(name, ty, body)`

其中 `ResolvedConst` 携带：

- `name`
- `const_id`
- `inst_ty`
- `schema_ty`

这使得常量在 elaboration 时就冻结到当时可见的 kernel identity，而不是只留下名字等待后续重查。

## 3. One-Shot Resolution

当前 parser bridge 采用两阶段：

1. `SynTerm -> RTerm`
2. `RTerm -> Term`

名称解析规则：

- 先查 `ParseEnv` 局部变量；
- 查不到再 resolve 常量；
- resolved constant 会记录 `ConstId` 与 schema-instance 关系；
- `=` 作为保留逻辑常量单独处理，不走普通 signature lookup。

这对应论文里的 one-shot resolution 目标：后续作用域变化不应改变旧解析结果的身份。

## 4. Core Typing

`elab_core_type_of(state, ctx, rterm)` 实现 resolved-term 上的独立类型检查。

关键点：

- `RVar` 按 `(name, ty)` 与局部上下文匹配。
- `RConst` 检查冻结的 `const_id` 仍对应同一 schema，并验证 `inst_ty ≼ schema_ty`。
- `RComb` 只接受函数类型应用。
- `RAbs` 在扩展上下文后检查 body。

因此 core typing 不依赖重新跑 named parser，也不依赖 tactic 层语义。

## 5. Boundary Lowering

当前支持：

- `elab_lower_to_term(rterm)`
- `elab_lower_to_db(rterm)`

lowering 策略：

- 对 named `Term`，保留 `name + inst_ty`，不把 frozen `const_id` 暴露到外部表示。
- 对 `DbTerm`，继续复用现有 typed De Bruijn lowering。

这让现有 kernel/tactics/prover 代码可以继续消费 `Term`/`Goal`，不需要一次性改造为直接消费 `RTerm`。

## 6. 当前边界

本轮实现明确不做：

- dictionary passing
- typeclass resolution
- metavariable / hole
- 局部类型推断
- higher-order unification

因此这里实现的是“论文第 7 节前半段的 runtime 对齐”，不是完整前端 elaborator。
