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
moon run src/cmd -- -d <file>
moon run src/cmd -- --no-warn <file>
```

`-d` 会输出完整 conclusion summary。`--no-warn` 会在只有 warning、
没有 error 时返回成功退出码。通过 `moon run` 启动时需要用 `--`
把后续参数转发给 QED CLI；编译成独立可执行文件后可直接运行
`qed-cmd -d --no-warn <file>`。

输入是 theorem-script 文件，例如：

```text
theorem truth_file : ⊢ T := by exact truth
```

仓库中的可运行示例见：

- `examples/truth_file.qed`
- `examples/demo_and.qed`
- `examples/and_comm.qed`
- `examples/multi_theorems.qed`
- `examples/multi_with_hole.qed`
- `examples/bad_branch.qed`
- `examples/unfinished_branch.qed`

仓库根目录下另有 `prelude/`，存放当前可直接运行的 theorem 资产文件；它们是
可运行脚本，不是当前 theorem-name catalog 的公开 surface。

## 文件形状

当前 shipped 的 theorem script 形状是：

```text
theorem <name> [(binder...)] : <goal> := by <steps>
```

当一个文件里写多个 theorem 时，用小写 `qed` 结束前一个 theorem block：

```text
theorem t1 : ⊢ T := by exact truth
qed

theorem t2 : ⊢ T := by exact truth
qed
```

其中：

- `<name>` 是 theorem 名。
- `[(binder...)]` 当前支持零个或多个 theorem-header binder。
- `<goal>` 是一个 sequent。
- `<steps>` 是 proof steps，可以写成单行顺序形式，也可以写成换行块状形式。

单 theorem 文件为了兼容既有示例，末尾可以省略 `qed`。多 theorem 文件中，前一个
theorem 必须在下一个顶层 `theorem` 之前写 `qed`。

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
qed
```

当前文档和示例里最稳妥的 file-first 用法，是先使用 `bool` binder。

### 当前支持的量词目标

下面这种 raw `forall` theorem goal 现在作为 goal-only sugar 被接受：

```text
theorem quant_raw_intro_ok : ⊢ forall (x : bool), x -> x := by
  intro h
  exact h
qed
```

parenthesized 写法也被接受：

```text
theorem quant_raw_intro_paren_ok : ⊢ (forall (x : bool), x -> x) := by
  intro h
  exact h
qed
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
qed
```

当步骤需要显式分支时，当前支持最小结构化 branch block：

```text
theorem demo_and (x : bool) : ⊢ x -> x ∧ x := by
  intro h
  split { exact h } { exact h }
qed
```

更像经典命题逻辑的例子：

```text
theorem and_comm (p : bool) (q : bool) : ⊢ p ∧ q -> q ∧ p := by
  intro h
  split { exact and_elim_r } { exact and_elim_l }
qed
```

```text
theorem bad_branch (x : bool) : ⊢ x -> x ∨ x := by
  intro h
  left { exact truth }
qed
```

## 当前最重要的限制

- 当前 `src/cmd` 工作流是 file-first；单 theorem 文件可省略末尾 `qed`，多 theorem 文件用 `qed` 分隔。
- 直接 runnable 的公开例子应优先使用 `examples/` 中已有脚本。
- theorem-header binder 已 shipped；raw `forall` theorem goal 作为 goal-only sugar 已支持，term-level 仍不支持。
- 不支持的路径必须 fail-closed，不会伪造 theorem success。
- `hole` 返回 unfinished，不返回 theorem success。

## 输出形状

当前 CLI 输出分三类：

- 成功：默认每个 theorem 输出一行 `ok <theorem_name>`；使用 `-d` 时输出
  `ok <theorem_name>: <conclusion_summary>`
- 失败：`error[kind] ...`
- 未完成：`warning[unfinished] ...`，不会产生 theorem authority，但会继续检查后续 theorem。

`moon run src/cmd -- -d --no-warn <file>` 中的 `--` 只属于 `moon run`
参数转发；独立可执行文件不需要它，直接用 `qed-cmd -d --no-warn <file>`。

更完整的失败字段、unfinished 字段和稳定示例见 `doc/manual.md`。
