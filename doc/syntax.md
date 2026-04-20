# QED Syntax Guide

Status: active
Audience: users, contributors
Authority: user-facing syntax reference for current shipped input surface; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/manual.md`
Scope: current theorem-script surface syntax, CLI-facing file shape, supported proof steps, and known unsupported forms
Last reviewed: 2026-04-20

本文档是 QED 当前 shipped 用户输入语法的速查表。

它只回答一个问题：`src/cmd` 当前到底接受什么样的 theorem script。关于能力边界、
支持矩阵、失败语义和实现合同，仍以 `doc/manual.md` 为主入口。

## 快速入口

当前命令行入口是：

```bash
moon run src/cmd <file>
```

输入是单个 theorem-script 文件，例如：

```text
theorem truth_file : ⊢ T := by exact truth
```

仓库中的可运行示例见：

- `examples/truth_file.qed`
- `examples/demo_and.qed`
- `examples/and_comm.qed`
- `examples/bad_branch.qed`
- `examples/unfinished_branch.qed`

## 文件形状

当前 shipped 的 theorem script 形状是：

```text
theorem <name> [(binder...)] : <goal> := by <steps>
```

其中：

- `<name>` 是 theorem 名。
- `[(binder...)]` 当前支持零个或多个 theorem-header binder。
- `<goal>` 是一个 sequent。
- `<steps>` 是 proof steps，可以写成单行顺序形式，也可以写成换行块状形式。

当前 `src/cmd` 的 file-first 工作流只处理单个 theorem script 文件。

## theorem 头

### theorem 名

最小例子：

```text
theorem truth_file : ⊢ T := by exact truth
```

### theorem-header binder

当前 shipped 的 binder 形式是：

```text
(x : bool)
```

例如：

```text
theorem id_bool (x : bool) : ⊢ x -> x := by
  intro h
  exact h
```

当前文档和示例里最稳妥的 file-first 用法，是先使用 `bool` binder。

### 当前支持的量词目标

下面这种 raw `forall` theorem goal 现在作为 goal-only sugar 被接受：

```text
theorem quant_raw_intro_ok : ⊢ forall (x : bool), x -> x := by
  intro h
  exact h
```

parenthesized 写法也被接受：

```text
theorem quant_raw_intro_paren_ok : ⊢ (forall (x : bool), x -> x) := by
  intro h
  exact h
```

也就是说：

- theorem-header binder `(x : bool)` 与 raw `forall` / `∀` theorem goal 都属于当前已 shipped 的量词面用户语法。
- raw `forall (x : A), body` / `∀ (x : A), body` 只在 theorem-script goal / `parse_goal` 入口上被接受，不是 term-level 语法。
- raw `forall` 这条路径当前只是 goal sugar；它沿用同一条 lowering / replay / CLI diagnostics 合同，不引入新的 kernel quantifier authority。

## goal 形状

当前 shipped surface 使用 sequent goal：

```text
⊢ goal
A ⊢ B
A, B ⊢ goal
```

README 和 `examples/` 里的最小 runnable examples 主要使用：

- `⊢ T`
- `⊢ x -> x`
- `⊢ x -> x ∧ x`
- `⊢ x -> x ∨ x`

对第一次使用 CLI 的用户，更稳妥的是从 `T`、`F` 和 theorem-header binder 的 state-free 例子开始。

## proof steps

当前 shipped 的 step 只有这几类：

- `intro`
- `exact`
- `apply`
- `assumption`
- `split`
- `left`
- `right`
- `hole`

### `intro`

```text
intro h
```

当当前目标是 `A -> B` 时，引入一个局部假设并继续证明后件。

### `exact`

```text
exact h
exact truth
```

用于直接闭合当前目标。

### `apply`

```text
apply and_elim_l
```

用于把 implication-backed theorem 或局部蕴含假设作用到当前目标上，产生新的子目标。

### `assumption`

```text
assumption
```

在当前局部假设中寻找与当前目标匹配的证据。

### `split`

顺序写法：

```text
split
```

结构化分支写法：

```text
split { exact h } { exact h }
```

### `left` / `right`

顺序写法：

```text
left
right
```

结构化分支写法：

```text
left { exact h }
right { right { hole h1 } }
```

### `hole`

```text
hole
hole h1
```

`hole` 不会伪造成功；当前会返回结构化 unfinished 结果。

## 顺序块与结构化分支块

当前 `<steps>` 可以写成单行：

```text
theorem t1 (x : bool) : ⊢ x -> x := by intro h; exact h
```

也可以写成多行块：

```text
theorem t1 (x : bool) : ⊢ x -> x := by
  intro h
  exact h
```

当步骤需要显式分支时，当前支持最小结构化 branch block：

```text
theorem demo_and (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
```

更像经典命题逻辑的例子：

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
```

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
```

## 当前最重要的限制

- 当前 `src/cmd` 工作流是 file-first，只接受单个 theorem-script 文件。
- 直接 runnable 的公开例子应优先使用 `examples/` 中已有脚本。
- theorem-header binder 已 shipped；raw `forall` theorem goal 作为 goal-only sugar 已支持，term-level 仍不支持。
- 不支持的路径必须 fail-closed，不会伪造 theorem success。
- `hole` 返回 unfinished，不返回 theorem success。

## 输出形状

当前 CLI 输出分三类：

- 成功：`ok <theorem_name>: <conclusion_summary>`
- 失败：`error[kind] ...`
- 未完成：`unfinished ...`

更完整的失败字段、unfinished 字段和稳定示例见 `doc/manual.md`。
