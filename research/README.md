# Research Notes

Status: research-only
Audience: maintainers, designers
Authority: non-authoritative design notes; subordinate to `doc/qed_formal_spec.pdf`, current code/tests, and `doc/governance.md`
Scope: unshipped design exploration, promotion gates, and go/no-go conclusions
Last reviewed: 2026-04-16

`research/` 用来放未 shipped 的设计研究档，不放当前实现合同。

这里的文档可以做三类事情：

- 记录某条研究线的最小设计边界；
- 定义 promotion gates、评估准入条件；
- 给出阶段性的 go/no-go 结论。

这里的文档不能做的事情：

- 代表当前 shipped capability；
- 高于 `doc/manual.md` 或 `doc/conformance.md`；
- 用研究原型去替代当前代码和测试事实。

当前研究主题：

- `research/rewrite-simplify/`
  rewrite/simplify 研究线，当前仍是 `research-only`，不在默认产品路径中。
