# Code Governance

Status: active
Audience: contributors, maintainers
Authority: repository code-organization policy; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/governance.md`
Scope: package layering, alias entrypoints, source responsibilities, and code-change documentation obligations
Last reviewed: 2026-04-18

本文档定义 QED 仓库的代码治理规则。它不增加新的语义规范层，只负责把包边界、alias 入口和文档回写义务固定下来，避免代码结构长期漂移。

## Layering

默认依赖方向固定为：

`kernel -> logic/elab -> parser -> tactics -> prover -> cmd`

治理要求：

- `kernel` 是唯一 theorem-construction boundary。
- `logic` 只能提供 checked helper、definition/unfold、replay helper 与 theorem catalog 组织，不得新增 primitive authority。
- `parser` 只负责文本语法、normalize、resolution 和 lowering；不得直接依赖 tactics execution object。
- `tactics` 只负责 goal-state transformation 和 replay orchestration；不得回写 parser 语义。
- `prover` 只做 parser/tactics/kernel 的编排与结构化诊断，不得成为新的逻辑权威。
- `cmd` 保持最薄外层，只消费稳定 facade，不新增低层知识。

若某次改动需要逆向依赖，默认视为设计问题；应优先引入中立数据结构或显式 bridge，而不是跨层直接引用。

## Alias Entry Points

每个包的官方 alias 入口固定为两类：

- `alias.mbt`
  生产源码入口。
- `alias_test.mbt`
  blackbox test 入口。

约束如下：

- `alias.mbt` 只暴露该包生产源码真实需要的稳定符号。
- `alias_test.mbt` 必须先镜像 `alias.mbt` 的生产导出，再补充 test-only imports。
- `alias_test.mbt` 不是第二套公共 API；不得形成与生产入口不同的导出哲学。
- alias 文件头注释必须说明入口适用范围和维护规则。
- 不得把 alias 当作无边界的下层符号转抄表。

## Source Responsibilities

单个文件或模块应尽量只承担一种主职责：

- 纯数据对象与 accessors
- 纯 lowering / normalization / rendering
- replay / orchestration
- corpus / mapping / fixtures

以下情况应优先拆分：

- 编排逻辑与错误渲染长期混在同一文件
- parser-side lowering 直接构造 tactics object
- façade 层文件逐渐演变成跨层杂糅入口

本仓库当前的首批治理样式包括：

- parser 输出 parser-owned `ParsedGoal`，由上层显式 bridge 到 `tactics.Goal`
- prover 保留编排角色，但继续把诊断渲染与 corpus 数据从主执行路径中分离

## Documentation Obligations

当代码改动影响以下内容时，必须同步回写文档：

- 公开能力口径
- 包职责或分层边界
- alias 入口语义
- 失败语义或结构化诊断字段

默认维护顺序：

1. 代码与测试
2. `doc/manual.md`
3. `doc/conformance.md`
4. `README.md`
5. `doc/current_workspace_audit.md`（仅在阶段结论变化时）

## Review Checklist

提交与 review 时至少核对：

- 新依赖是否符合既定分层
- `alias.mbt` / `alias_test.mbt` 是否仍是单一官方入口
- 是否把 parser/tactics/prover 的职责重新耦合在一起
- `.mbti` 变化是否符合预期公开边界
- 文档是否同步反映新的 shipped state
