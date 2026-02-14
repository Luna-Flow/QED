## 本轮目标与范围

- 目标：完成规范收口，确保 `INST_TYPE` 与 `DefOK`/`TypeDefOK` 的结构化连接在规则层显式可见，且审稿人不需要跨多个章节才能理解安全性来源。
- 范围：
  - 文稿一致性清扫（术语、状态模型、非空类型语义）；
  - `INST_TYPE` 规则重写（前提、失败分类、桥接说明）；
  - 审稿完整包产出（主文稿 + PDF + 本变更日志）。
- 不在范围：内核实现代码改动。

## 逐节变更（Section-by-Section）

- `== Global Theory State vs Local Scope State`（`doc/qed_formal_spec.typ:208`）
  - 明确 `(T, S)` 双层状态模型：`T` 为全局理论历史，`S` 为局部可弹栈可见层。
  - 新增 `DefHeads(T)` 单调性与 pop 不回滚定义历史的命题。
  - 增加“可实现为 tombstone registry”的等价实现视图。

- `== Type Constructor Extension Discipline`（`doc/qed_formal_spec.typ:257`）
  - 新增 `TypeDefOK` 类型扩展准入条件与规则步。
  - 引入“无空类型逃逸”构造不变式，将非空性从裸假设迁移为可审计门禁约束。

- `= Definitional Extension Discipline` 与 `== Definition Admissibility Judgment`（`doc/qed_formal_spec.typ:694`、`doc/qed_formal_spec.typ:731`）
  - 将定义头新颖性统一为 `c ∉ DefHeads(T)`（替代易歧义的当前可见性检查）。
  - 保留并强化 `TVars(r) ⊆ TVars(tau)` 作为规范性条件，持续封堵 ghost-type 漏洞。

- `= Global Admissibility Envelope`（`doc/qed_formal_spec.typ:763`）
  - 扩展 envelope：除 `DefOK` 外，新增 `TypeDefOK` 作为类型扩展必要门禁。

- `== Rule Schema: INST_TYPE`（`doc/qed_formal_spec.typ:1052`）
  - 从泛化 `valid(theta)` 重写为结构化前提：
    - `valid_ty_subst(theta)`；
    - `admissible_ty_image(T, theta)`；
    - `def_inst_coherent(theta, A_p ⊢ p)`。
  - 失败分类扩展到 5 条，并与上述前提一一对应。
  - 新增 Bridge Note，显式说明与 `DefOK`/`TypeDefOK`/Global Envelope 的闭环关系。

- `== Signatures and Symbols` / `== Constant Type Schemes and Instance Relation`（`doc/qed_formal_spec.typ:104`）
  - 引入常量主类型模式 `kappa_c : tau_gen` 与实例关系 `tau preceq tau_gen`。
  - 明确常量实例化是规范层一等关系，不再要求“项内类型 == 注册类型”逐字同一。

- `== Core Typing over Resolved Terms`（`doc/qed_formal_spec.typ:372`）
  - `RConst` 规则从“精确等型匹配”改为“主模式 + 实例关系”匹配。
  - 新增多态常量实例化可用性引理，明确系统不是单态锁死。

- `= Soundness Strategy` 与依赖图（`doc/qed_formal_spec.typ:1132`、`doc/qed_formal_spec.typ:1152`）
  - 义务从 4 项扩展为 5 项，单列“类型层非空保持”。
  - 依赖图新增 `Type Admissibility + TypeDefOK` 与 `Type Non-Emptiness Preservation` 节点。

- `== Semantic Assumptions`（`doc/qed_formal_spec.typ:1190`）
  - 将“所有类型非空”由单条全局假设收敛为：
    - 基础 prelude 非空假设；
    - 在 `TypeDefOK` 前提下的全局非空保持定理。

- 附录更新（`doc/qed_formal_spec.typ:1301` 之后）
  - Appendix A：`INST_TYPE` 依赖项增加 `TypeDefOK` 与 definitional coherence。
  - Appendix B：检查项补充 type gate 与 state history 分离。
  - Appendix C：扩展为 Definition + State 场景并加入 pop-then-redefine 拒绝用例。
  - Appendix D：新增 type soundness 审计场景。

## 审计问题对照矩阵（Issue -> Fix -> Location -> Residual Risk）

| Issue | Fix | Location | Residual Risk |
|---|---|---|---|
| Ghost Type Variable（定义体自由类型变量逃逸） | 强制 `TVars(r) ⊆ TVars(tau)` + `INST_TYPE` Bridge Note + `def_inst_coherent` 前提 | `doc/qed_formal_spec.typ:701`, `doc/qed_formal_spec.typ:1052` | 低（仍需实现层严格按同条件执行） |
| Empty Type Semantic Escape（空类型语义逃逸） | 新增 `TypeDefOK` + 非空见证门禁 + 非空保持定理 | `doc/qed_formal_spec.typ:257`, `doc/qed_formal_spec.typ:1190` | 低-中（若未来扩展 typedef 语法需保持见证规则） |
| Stack vs Theory 不一致（pop 后重定义歧义） | 分离 `(T,S)`；定义头新颖性绑定 `DefHeads(T)`；pop 不回滚历史 | `doc/qed_formal_spec.typ:208`, `doc/qed_formal_spec.typ:694` | 低（UI 层仍需展示内核身份避免符号混淆） |
| `INST_TYPE` 审稿不可追踪（需跨章猜测） | 规则内显式加入 admissibility 锚点与失败映射 | `doc/qed_formal_spec.typ:1052` | 低 |
| De Bruijn Type Erasure（内核层类型擦除） | 将 De Bruijn 核心语法改为显式携带类型标签（`DAbs(tau, ...)`, `DBound(..., tau)`），并将 `TRANS`/`BETA` 匹配条件改为 typed-core guard | `doc/qed_formal_spec.typ:439`, `doc/qed_formal_spec.typ:886`, `doc/qed_formal_spec.typ:977` | 低（要求实现严格保持边界 lowering 的类型标签） |
| Polymorphism Lockout（多态常量实例化锁死） | 引入常量主模式与实例关系 `tau ≼ tau_gen`，并在 elaboration/core typing/`INST_TYPE` 中加入实例守卫 | `doc/qed_formal_spec.typ:125`, `doc/qed_formal_spec.typ:379`, `doc/qed_formal_spec.typ:1109` | 低（实现需按同一实例判定关系执行） |

## 增量修订（De Bruijn 类型擦除审计）

- `== De Bruijn Shifting (for BETA)`（`doc/qed_formal_spec.typ:439`）
  - 从无类型构造（`Abs(t)`, `BVar(k)`）改为 typed core 构造（`DAbs(tau, t)`, `DBound(k, tau)`）。
  - `beta` 收缩规则补充 binder/argument 类型一致性侧条件。
  - 新增 typed-core injectivity 不变量，禁止跨域类型的抽象被结构等同。

- `== Boundary Conversion Properties`（`doc/qed_formal_spec.typ:510`）
  - 新增 Type-Sensitive Core Matching 引理，明确 boundary lowering 不擦除 binder-domain 类型标签。

- `== Rule Schema: TRANS`（`doc/qed_formal_spec.typ:865`）
  - 新增 typed De Bruijn core 匹配前提与对应失败项，防止中间项按“擦除后结构”误配。

- `== Rule Schema: BETA`（`doc/qed_formal_spec.typ:954`）
  - redex 形状改写为 typed 版本；
  - 失败分类新增 binder-domain label mismatch；
  - antecedent form 显式包含 `type_of(u) = tau`。

- 附录增强：
  - Appendix A 补充 `TRANS`/`BETA` 的 typed-core 依赖项；
  - Appendix B 增加 De Bruijn 类型敏感匹配检查项；
  - 新增 Appendix E（Typed De Bruijn Core Audit Scenarios）。

## 增量修订（Polymorphism Lockout 审计）

- `== Constant Type Schemes and Instance Relation`
  - 新增常量主模式 `kappa_c : tau_gen` 与实例关系 `tau ≼ tau_gen`。
  - 明确常量在核心中以“主模式 + 实例化类型”合法，不再要求逐字等型。

- `== Named Elaboration Judgment` 与 `== Core Typing over Resolved Terms`
  - `RConst` 的 elaboration/core typing 前提都切换为实例关系判定。
  - 新增“Polymorphic Constant Instantiation Admissibility”引理与 “No Monomorphic Lockout” 说明。

- `== Rule Schema: INST_TYPE`
  - 新增常量实例一致性侧条件：`tau_i ≼ tau_gen(kappa_c)`。
  - 失败分类补充 constant-instance mismatch。
  - Bridge Note 增加常量实例守卫与表达能力说明。

- 附录增强：
  - Appendix A 增加 `INST_TYPE` 对常量实例关系的依赖项；
  - Appendix B 增加 `tau ≼ tau_gen` 检查项；
  - Appendix D 增加多态常量实例化审计场景（`id` 在 `bool/int` 实例下可用）。

## 验收清单（Checklist with pass/fail）

- [PASS] `INST_TYPE` 小节显式引用 `DefOK`、`TypeDefOK`、Global Admissibility Envelope。
- [PASS] 全局历史语义统一为 `DefHeads(T)`，且与局部 `pop` 行为分离。
- [PASS] 非空类型语义从裸假设迁移到 `TypeDefOK` 门禁 + 保持定理叙事。
- [PASS] 文稿附录包含 Ghost/Empty/Pop-Redefine 回归场景。
- [PASS] De Bruijn 核心改为显式类型标注并在 `TRANS`/`BETA` 规则中被强制检查。
- [PASS] 多态常量使用通过 `tau preceq tau_gen` 实例关系开放，避免单态锁死。
- [PASS] 编译检查通过：
  - 命令：`typst compile doc/qed_formal_spec.typ doc/qed_formal_spec.pdf`
  - 结果：成功生成 `doc/qed_formal_spec.pdf`。

## 未决项（若无则写 None）

None。
