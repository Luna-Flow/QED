# Documentation Governance

Status: active
Audience: contributors, maintainers
Authority: repository documentation policy; subordinate to `doc/qed_formal_spec.pdf`
Scope: document hierarchy, naming, metadata, and cross-reference rules
Last reviewed: 2026-04-16

本文档定义 QED 仓库的文档治理规则。目标不是增加新的规范层，而是把现有文档按权威性、用途和受众硬性分层，避免同一主题在多个入口里重复叙述并逐渐漂移。

## Document Layers

QED 当前采用以下文档层级：

1. 规范层
   `doc/qed_formal_spec.pdf` 是唯一规范性来源，`doc/qed_formal_spec.typ` 是其源文件。
2. 实现层
   当前代码与回归测试决定真实 shipped state。
3. 实现文档层
   `doc/manual.md`、`doc/conformance.md`、`doc/current_workspace_audit.md` 描述当前实现合同、工程符合性和阶段性审计。
4. 摘要与导航层
   `README.md`、`application.typ` 只做摘要和入口导航，不得高于实现层和实现文档层。
5. 研究层
   `research/` 只承载未 shipped 的设计研究、promotion gates、go/no-go 结论和原型评估。研究文档不是产品合同。

若代码与文档冲突，先以代码 + 测试核定真实状态，再回写实现文档。
若实现与论文规范冲突，论文规范仍为准。

## Canonical Entry Points

每类信息必须有单一主入口：

- 当前实现合同：`doc/manual.md`
- 工程符合性与代码/测试映射：`doc/conformance.md`
- 阶段性风险与缺口：`doc/current_workspace_audit.md`
- 仓库摘要与快速入口：`README.md`
- 研究目录入口：`research/README.md`

其他文档只能补充，不得平行复制“当前状态”。

代码组织与 alias 入口治理由 `doc/code_governance.md` 统一定义；它不高于当前代码与实现文档，只负责固定工程边界和维护义务。

## Metadata Contract

除顶层 `README.md` 与规范正文外，面向维护的文档头部都应包含：

- `Status`
- `Audience`
- `Authority`
- `Scope`
- `Last reviewed`

状态标签使用以下词汇：

- `active`
- `point-in-time audit`
- `research-only`
- `superseded`
- `archival reference`

## Naming Rules

- 实现文档使用职责导向命名，如 `manual.md`、`conformance.md`、`current_workspace_audit.md`。
- 研究文档使用主题目录 + 阶段文件名，统一采用 lowercase kebab-case。
- 新研究主题应放在 `research/<topic>/` 下，例如 `research/rewrite-simplify/`。
- 不再新增 `v2`、`new`、`tmp`、`final` 这类临时命名；需要替代时直接完成迁移并删除旧入口。

## Content Rules

- `README.md` 只允许写：
  - 项目简介
  - 当前 shipped subset 的高层摘要
  - 构建命令
  - 文档地图
- `README.md` 不应承载：
  - 完整支持矩阵
  - 长篇能力列表
  - 审计细节
  - 未来计划细节
- `doc/manual.md` 描述当前实现边界、模块职责、支持矩阵和稳定示例。
- `doc/conformance.md` 描述规范对齐、代码/测试映射、贡献者检查项和文档示例约束。
- `doc/current_workspace_audit.md` 只记录某一时间点仍然成立的风险、缺口和 follow-up，不长期重复 manual/conformance 的稳定事实。
- `research/` 文档必须显式声明 `research-only`、`not shipped`、`non-authoritative`。

## Example And Reference Rules

- 公开宣称的 capability 必须能回溯到当前代码和回归测试。
- public runnable example 必须锚定到现有测试；不得在文档中发明未测试脚本。
- `README.md` 只摘要能力，不单独发明示例语义。
- research 文档可以引用 shipped 状态，但应链接到实现文档，而不是重复写一份长期状态说明。

## Current Document Map

- `README.md`
  仓库摘要与导航入口。
- `doc/manual.md`
  当前实现合同。
- `doc/conformance.md`
  代码/测试映射与工程符合性。
- `doc/code_governance.md`
  包分层、alias 入口与代码维护义务。
- `doc/current_workspace_audit.md`
  当前工作区阶段性审计。
- `doc/TRICK.md`
  Typst 维护速记，属于规范源的辅助笔记，不属于实现合同。
- `doc/qed_formal_spec_changelog.md`
  规范变更记录，属于规范维护辅助材料。
- `research/README.md`
  研究目录入口与边界声明。

## Maintenance Rule

当一次改动同时影响实现、公开能力口径和研究判断时，应按下面顺序维护：

1. 代码与测试
2. `doc/manual.md`
3. `doc/conformance.md`
4. `README.md`
5. `doc/current_workspace_audit.md`
6. 相关 `research/` 文档
