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

## 增量修订（构造性闭包版）

- 将 `SpecOK` 小节中的 *Theorem Goal* 升级为正式定理，并补入“单步 spec 头消去”的构造性证明法：
  - 在文稿内定义 `erase_spec` 递归消去器；
  - 给出基于导出树大小的良基归纳不变式。
- 新增 `Constructive Closure: Derivation Objects and Erasure Operators` 小节：
  - 引入有限导出对象 `Derives(D, s)`；
  - 明确 `erase_def` / `erase_spec` / `erase_typedef` 三类消去器；
  - 给出三条对应正确性定理（旧语言句子保持）。
- 将 `Meta-Theorem Target` 升级为正式全局保守性元定理：
  - 显式写出有限扩展序列上的逐步回擦组合证明；
  - 由每步 gate 消去正确性推出全局 `T' ⊢ φ => T ⊢ φ`。
- 文档状态与 P0 checklist 同步更新：
  - `Current Status` 改为“文稿内构造性闭包已给出”；
  - checklist 新增“导出对象系统”与“分 gate 消去 + 组合定理”两项。

## 增量修订（双分区与权威边界）

- 在主文稿前部新增 `Part I: Logic Core (Normative)` 与 *Authority Contract*：
  - 明确 Part I 是唯一逻辑规范源；
  - 明确 De Bruijn 与 scope 属于逻辑正确性机制，不是可选工程细节。
- 将工程段入口重命名为 `Part II: Engineering Realization (Informative + Conformance)`：
  - 显式声明 Part II 下游于 Part I，不得反向定义逻辑。
- 新增 `Conformance Obligations (Part I -> Part II)` 子节：
  - 规则一致性、边界一致性、scope 稳定性、gate 一致性、证书非权威性五条实现符合性义务。
- `Documentation Maintenance Notes` 首句改写为双分区维护口径：
  - Part I 作为逻辑真源维护；
  - Part II 作为对 Part I 的符合性报告层维护。

## 增量修订（De Bruijn / Scope 证明强化）

- 在 De Bruijn 小节新增三条桥接定理：
  - `Lowering Preserves Typing`；
  - `Lifting Preserves Typing up to Alpha`；
  - `Boundary Commutation with Capture-Avoiding Substitution`。
- 将 scoped shadowing 三条命题由 proof sketch 改为完整证明文本（按定义逐步推出）。
- 新增 `Resolution Freeze under Scope Mutation` 定理：
  - 形式化声明已解析项在后续 `push/add/pop` 序列下的前提不变性；
  - 明确 scope 仅影响未来命名解析，不回写既有 resolved 对象。

## 增量修订（Phase 自动推进：Part I 去工程化 + Part II 收敛）

- Part I 文案去工程绑定化（不改逻辑内容）：
  - Abstract 从 “implementation-aware specification” 改为 “formal mathematical specification”；
  - `Type Grammar` / `Term Grammar` 的 “In implementation terms” 改写为 “One canonical concrete representation”；
  - boundary/scope 段落中的 API/实现措辞改写为抽象语义措辞（保持可实现性但不依赖某一实现）。
- `MK_COMB` 小节由 `Type Preservation Sketch` 升级为 `Type Preservation Theorem`：
  - 保留原推导结构并补为完整“Proof.”结尾样式。
- Part II 收敛为符合性语义：
  - error taxonomy 对齐段由 “normative for final API” 改为 “conformance target for engineering realizations”；
  - Appendix B 尾句改为 “logic-closure + conformance/regression gate”。

## 增量修订（Phase 自动推进：Part II 符合性闭包）

- `Engineering Correspondence` 补充“informative only”边界声明：
  - 模块映射仅用于审计覆盖，不改变 Part I 的任何定义/定理。
- 新增 `Conformance Transfer Theorem` 小节：
  - 定义 `Faithful Realization`（满足五条 conformance obligations）；
  - 给出实现到逻辑的传递定理：若实现接受 sequent $s$，则 Part I 可导出 $s$；
  - 证明法采用 acceptance trace 重建：规则映射、边界引理替换、scope 稳定性擦除、gate 对应、证书事件丢弃。
- Primitive Rules 引导段去实现耦合：
  - 将 “parallel with implementation updates” 改为 “Part I side conditions are authoritative”。

## 增量修订（Phase 自动推进：Primitive Rules 构造性闭包增强）

- 在 `Rule Schema` 章节末新增 `Rule-Level Constructive Preservation Capsules`：
  - 统一给出 `Preserve_R : valid(Premises_R) => valid(Conclusion_R)` 的构造性模板；
  - 为 10 条 primitive rules 分别给出胶囊化保持声明（含 `INST_TYPE` 的 gate/coherence/instance 三重约束）；
  - 新增 `Rule Capsule Closure` 汇总定理，明确“逐规则案例分析 + 胶囊调用”即可构成 P1 义务闭包。

## 增量修订（Phase 自动推进：双分区审计清单闭环）

- Appendix B（P0 checklist）扩展 Part II 一致性项：
  - 新增 24-28 条，覆盖 Part II 下游声明、五项 conformance obligations、transfer theorem、非权威映射、error taxonomy 的 conformance 定位。
- 新增 Appendix G `Part II Conformance Audit Scenarios`：
  - Rule-fidelity replay；
  - Boundary-fidelity；
  - Scope-fidelity stability；
  - Gate-fidelity；
  - Certificate non-authority。
- 至此形成 “Part I 逻辑闭包 + Part II 符合性闭包” 双审计结构。

## 增量修订（Phase 自动推进：语义假设包与一致性层补强）

- 在 `Semantic Assumptions` 下补入模型类封装：
  - 新增 `Admissible Model Class` 定义（typing/denotation + Choice + Infinity anchor + gate-admitted定理）。
  - 新增 `Model-Class Non-Emptiness` 假设，显式化“非平凡模型存在”前提。
- 新增一致性转移结论：
  - `Semantic Non-Triviality Transfer`（反模型推出不可导）；
  - `Consistency Witness Form`（在同一模型类语义下排除同句与其否定的同时可导）。

## 增量修订（Phase 自动推进：声明-证明追溯矩阵）

- 新增 Appendix H `Claim-to-Proof Trace Matrix`：
  - 给出 C1..C10 十条高层主张到“定义锚点/证明锚点”的短路径映射；
  - 覆盖 rule soundness、三类 gate conservativity、scope/boundary 稳定性、global conservativity、conformance transfer、non-triviality、certificate non-authority。
- 附录尾部新增 review rule：
  - 每条主张目标为 “claim -> definition -> theorem” 三步可达，便于审稿与交叉复核。

## 增量修订（Phase 自动推进：术语一致性精修）

- Part I 术语进一步去工程化并统一：
  - `external modules` 改为 `external contexts`；
  - `implementation-level check` 改为 `admission-procedure check`；
  - `module boundaries and test responsibilities` 改为 proof-block 视角叙述；
  - infinity-anchor 与 canonical-theorem 处的 `implementation` 用词替换为 realization/presentation 语义。
- 维护说明与审计场景同步统一措辞：
  - `APIs evolve` 改为 `realization interfaces evolve`；
  - Appendix F 的 schema widening 场景改为 admission-procedure 语义。
- Notation 统一：
  - 语义解释记号统一为 `"denote"(t, rho, M)`，与后文 boundary denotation 引理保持同一参数约定。

## 增量修订（Phase 自动推进：闭环锚点补齐）

- 在 Part II `Audit Certificates and Replay Interface` 补齐缺失定义锚点：
  - 新增 `Admissible(T, t_h)` 定义（由 Part I `Derives` 对象与 gate 合法性见证）；
  - 新增 `SentenceInLanguage(T_0, t_h)` 定义（闭句 + base language 符号约束）。
- `ConservativeReplayOK` 现在使用已显式定义的谓词，不再依赖隐式语义前提。

## 增量修订（符号书写一致性修复）

- 修复替换记号中的斜杠书写一致性：
  - 将 `t[s/x]` 统一为 `t[s\/x]`；
  - 与文中既有 `s[u\/x]` 记法保持一致，避免 `[A/B]` 形式在审阅与渲染中产生歧义。

## 增量修订（语气优化）

- 全文语气向“论文叙述风格”收敛，保持逻辑内容不变：
  - `Authority Contract` 调整为 `Normative Scope`，并将部分强命令式句型改为学术叙述句型；
  - Part II 开场从“实现钩子”口径改为“具体 realization 与 conformance 记录”口径；
  - `Documentation Maintenance Notes` 改为 `Concluding Remarks`，`Near-term maintenance focus` 改为 `Future refinement directions`。
- 附录语气统一：
  - `Audit Scenarios` 统一改为 `Validation Scenarios`；
  - 末尾由 “required before claiming” 改为 “provide structured evidence for ...”。
- 细节语义一致性：
  - 语义解释记号统一为 `"denote"(t, rho, M)`（与后文 denotation 引理一致）；
  - `ConservativeReplayOK` 相关谓词在文中具名定义，减少隐式术语。
