
# Parser V0.5（Term + Goal + theorem-by + Lean-like Decls）

本文档描述当前 `src/parser` 包的稳定能力、语法边界与调用方式，作为上层模块（`tactics/prover/cmd`）的标准入口说明。

## 1. 目标与边界

- 目标：提供“文本语法 -> AST -> resolved elaboration -> bridge 到 `tactics`”的统一路径。
- 当前范围：`Term + Goal + theorem-by(raw) + let/def`。
- 不在范围：
  - 多参数/模式匹配 `def`
  - `lambda` 文本语法
  - 字典传递/约束求解/mvar
  - 分支 proof script 块

## 2. 公共 API

来自 `src/parser/pkg.generated.mbti`：

- `parse_term_raw(src : String) -> Result[SynTerm, ParseError]`
- `parse_goal_raw(src : String) -> Result[SynGoal, ParseError]`
- `parse_theorem_script_raw(src : String) -> Result[SynTheoremScript, ParseError]`
- `parse_term(state, src) -> Result[Term, ParseBridgeError]`
- `parse_goal(state, src) -> Result[Goal, ParseBridgeError]`
- `parse_resolved_term_with_env(state, env, src) -> Result[RTerm, ParseBridgeError]`
- `parse_term_with_env(state, env, src) -> Result[Term, ParseBridgeError]`
- `parse_goal_with_env(state, env, src) -> Result[Goal, ParseBridgeError]`
- `lower_syn_term_with_env(state, env, syn) -> Result[Term, ParseBridgeError]`
- `lower_syn_goal_with_env(state, env, syn) -> Result[Goal, ParseBridgeError]`
- `empty_parse_env() -> ParseEnv`
- `parse_let(env, src) -> Result[ParseEnv, ParseBridgeError]`
- `parse_def_function(state, env, src) -> Result[(KernelState, Thm), ParseBridgeError]`

## 3. 语法

### 3.1 Term

支持：

1. `Name`：`P`、`f`、`foo_bar1`
2. 应用：`f x`、`f x y`
3. 前缀否定：`¬ t`、`\not t`
4. 中缀：`=`, `∧`, `∨`, `->`, `\imp`
5. 括号：`(f x) = y`
6. 别名：`\and`, `\or`

近似文法：

```text
Term := Prefix (Op Prefix)*
Prefix := ('¬' | '\not') Prefix | App
Op := '=' | '∧' | '∨' | '->' | '\imp' | '\and' | '\or'
App := Atom Atom*
Atom := Name | '(' Term ')'
Name := [A-Za-z_][A-Za-z0-9_]*
```

### 3.2 Goal

- `H1, H2 |- C`
- `H1, H2 ⊢ C`
- `|- C` / `⊢ C`

### 3.3 theorem-by 脚本（raw）

```text
TheoremScript := 'theorem' Name ':' Goal ':=' 'by' Step (';' Step)*
Step :=
  'intro' Name |
  'exact' Name |
  'apply' Name |
  'assumption' |
  'split' |
  'left' |
  'right'
```

说明：

- 这里只做 raw parsing，不直接执行 tactic。
- 执行由 `prover` 包完成。

### 3.4 `let` 声明

```text
LetDecl := 'let' Name ':' Type
Type := TypeAtom ('->' Type)?   // 右结合
TypeAtom := Name | '(' Type ')'
```

### 3.5 `def` 声明（单参数）

```text
DefDecl := 'def' Name '(' Name ':' Type ')' ':' Type '{' Term '}'
```

## 4. 固定优先级与结合性

采用“先解析中缀链，再做 fixity 重排”的 GHC 风格流程。

优先级从高到低：

1. application
2. `¬`
3. `∧`
4. `∨`
5. `->`
6. `=`

结合性：

- `->` 右结合
- `∧/∨` 左结合
- `=` non-assoc（`a = b = c` 报 `NonAssocChain`）

## 5. Bridge 规则（SynTerm -> RTerm -> kernel.Term）

- `Name`：先查 `ParseEnv`，后 resolve 常量。
- `Prefix("¬", t)`：resolve 为 `RConst(not)` 应用。
- `Infix("->", a, b)`：resolve 为 `RConst(imp)` 应用。
- `Infix("∧", a, b)`：resolve 为 `RConst(and)` 应用。
- `Infix("∨", a, b)`：resolve 为 `RConst(or)` 应用。
- `Infix("=", a, b)`：resolve 为内建 equality constant 应用。
- resolve 成功后再统一 lower 回 kernel `Term`。
- `Infix("=", a, b)`：`elab_eq`。

Name lowering 决策：`local > const`。

连接词依赖：

- `not/imp/and/or` 必须已在 state 中注册，否则返回 `ParseBridgeError::Sig(UnknownConst)`。

## 6. De Bruijn 语义说明

parser 输出仍是 named `Term`，但 kernel 的 alpha/闭包检查是 De Bruijn 语义：

- `let` 局部对应 `FVar(...)`。
- `def f(x : A) : B { body }` 中 `x` 在函数体对应 `BVar(0)`。
- 若定义体残留自由变量，`ks_define_const_thm` 报 `DefinitionNotClosed`。

## 7. 错误类型

### 7.1 `ParseErrorCode`

- `UnexpectedToken`
- `UnexpectedEof`
- `MissingTurnstile`
- `NonAssocChain`
- `UnknownOperator`
- `EmptyConclusion`
- `EmptyHypothesis`

`ParseError` 含：`code + offset + detail`。

### 7.2 `ParseBridgeError`

- `Parse(ParseError)`
- `Sig(SigError)`
- `Logic(LogicError)`

## 8. 示例

### 8.1 Goal 解析

```moonbit
let g = expect_ok(parser.parse_goal(st, "P, Q ⊢ P"))
```

### 8.2 theorem 脚本 raw 解析

```moonbit
let s = expect_ok(
  parser.parse_theorem_script_raw(
    "theorem t : ⊢ P -> P := by intro h; exact h",
  ),
)
```

### 8.3 let + def

```moonbit
let env1 = expect_ok(parser.parse_let(parser.empty_parse_env(), "let x : A"))
let (st1, _th) = expect_ok(
  parser.parse_def_function(st0, env1, "def id(y : A) : A { y }"),
)
```

## 9. 当前边界（2026-03-08）

1. 支持线性 theorem-by raw parser，不支持分支块。
2. 支持 `¬/->/∧/∨/=` 解析与 lowering。
3. 不支持量词、lambda 文本、多参数 def、约束求解。
