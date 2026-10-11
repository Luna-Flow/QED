# Theory proof continuation

- Status: Typed HOL mainline complete; MoonBit refinement excluded
- Audience: specification maintainers
- Authority: Part I of `doc/attachments/qed_formal_spec.typ`
- Scope: mathematical theory only; MoonBit refinement and issue #15 are deferred by the user
- Last reviewed: 2026-10-12

## Semantic basis and decisions

The existing `Lean.Expr` pack is a conditional approximation, not a typed HOL model.
Do not discharge its stronger obligations by adding another law field. The normative
proof is the intrinsically typed, De Bruijn HOL calculus with actual function carriers
and boolean truth values. The legacy pack is archival and is excluded from the default
`QEDFV` target; its remaining correspondence obligations are MoonBit refinement work.
The normative DEDUCT rule discharges assumptions; it has no union-equality side condition.
Choice is classical Hilbert selection, and `ind` is interpreted by the natural numbers.
Typedef carriers must be witnessed predicate subtypes, uniformly in type parameters.

## Inventory and acceptance matrix

| Row | Cause / required change | Acceptance | State |
| --- | --- | --- | --- |
| T1 / P1 | Legacy syntax does not enforce HOL typing. Add type-indexed syntax, typed variables and valuations. | Lean checks construction and carrier nonemptiness; explicitly track legacy correspondence. | Typed HOL complete; legacy correspondence is MoonBit refinement |
| T2 / P6 | Substitution and beta laws are assumed. Prove renaming, capture-avoiding substitution and evaluation commutation. | Universal Lean theorems, including under binders. | typed core complete |
| T3 / I8 / P7 | Legacy DEDUCT needs a false side condition. Prove the exact discharge rule from boolean equality. | Model-independent indexed derivations prove all primitive rules for every interpretation under `ChoiceNatural`. | typed core complete |
| T4 / I6 / P7 | No concrete model or nontriviality. Construct equality, Choice, infinite `ind`, and a false sentence. | Closed false sentence is not derivable; no custom axioms. | typed model and non-derivability complete |
| T5 / I3 / P3 | Definition gate has a shallow occurrence check and no equation derivation. Add recursive support and fresh closed typed definitions. | Typed fresh-constant equation and old-language validity iff. | Typed HOL complete; legacy gate correspondence is MoonBit refinement |
| T6 / I2 / P4 | Typedef contract is syntactic/vacuous. Build witnessed predicate subtypes and Abs/Rep functions. | All three equations for every parameter valuation and actual nonempty carriers. | Typed HOL complete; signature bridge is MoonBit refinement |
| T7 / I4 / P5 | Specification gate checks the wrong witness shape. Derive the property through Choice and definition. | Typed fresh-constant interpretation, Choice property, and old-language validity iff. | Typed HOL complete; legacy gate correspondence is MoonBit refinement |
| T8 / P8 | Same-state erasure is insufficient for an implementation theorem. | Typed HOL proves finite old-language semantic conservativity; distinct-state syntactic simulation is MoonBit refinement. | complete for mathematical theory; implementation-open boundary |
| T9 / P2 | Scope/history is partly structural. Preserve the proven structural results and track theory correspondence. | Typed HOL has immutable resolved identities; concrete scope/history correspondence is MoonBit refinement. | complete for mathematical theory; implementation-open boundary |
| T10 / P9 / #15 | MoonBit refinement / provenance bug. | Deferred by explicit user instruction. | out of scope |
| T11 | Proof-status documentation must match theorem statements. | Build, axiom inspection and a reconciled status ledger. | complete |

## Ordered work and verification

1. Build typed syntax and concrete interpretation; prove substitution lemmas locally. **Complete for the typed core.**
2. Prove exact rules and consistency by derivation induction. **Complete for the typed primitive core.**
3. Construct semantic extension contracts and finite semantic conservativity.
4. Keep named/De Bruijn, executable gate correspondence, and state-lineage simulation
   explicitly outside the Typed HOL proof until the MoonBit refinement is undertaken.
5. Run targeted Lean checks, project build and `#print axioms` on the main results;
   update the specification/audit ledger and existing PR.

The remaining risks are confined to the excluded implementation boundary. Model
extension is reported as semantic conservativity; it is not called syntactic
conservativity because that would require a completeness theorem or an explicit
derivation translation for the executable kernel.
