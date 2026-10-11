# Theory proof continuation

- Status: active
- Audience: specification maintainers
- Authority: Part I of `doc/attachments/qed_formal_spec.typ`
- Scope: mathematical theory only; MoonBit refinement and issue #15 are deferred by the user
- Last reviewed: 2026-10-12

## Semantic basis and decisions

The existing `Lean.Expr` pack is a conditional approximation, not a typed HOL model.
Do not discharge its stronger obligations by adding another law field. Construct an
intrinsically typed, De Bruijn HOL calculus with actual function carriers and boolean
truth values instead. Keep the legacy pack visible until correspondence is proved.
The normative DEDUCT rule discharges assumptions; it has no union-equality side condition.
Choice is classical Hilbert selection, and `ind` is interpreted by the natural numbers.
Typedef carriers must be witnessed predicate subtypes, uniformly in type parameters.

## Inventory and acceptance matrix

| Row | Cause / required change | Acceptance | State |
| --- | --- | --- | --- |
| T1 / P1 | Legacy syntax does not enforce HOL typing. Add type-indexed syntax, typed variables and valuations. | Lean checks construction and carrier nonemptiness; explicitly track legacy correspondence. | typed core complete; correspondence active |
| T2 / P6 | Substitution and beta laws are assumed. Prove renaming, capture-avoiding substitution and evaluation commutation. | Universal Lean theorems, including under binders. | typed core complete |
| T3 / I8 / P7 | Legacy DEDUCT needs a false side condition. Prove the exact discharge rule from boolean equality. | Induction proves all primitive rules for the constructed semantics. | typed core complete |
| T4 / I6 / P7 | No concrete model or nontriviality. Construct equality, Choice, infinite `ind`, and a false sentence. | Closed false sentence is not derivable; no custom axioms. | active |
| T5 / I3 / P3 | Definition gate has a shallow occurrence check and no equation derivation. Add recursive support and fresh closed typed definitions. | Checked definition equation and cross-theory expansion. | active |
| T6 / I2 / P4 | Typedef contract is syntactic/vacuous. Build witnessed predicate subtypes and Abs/Rep functions. | All three equations for every parameter valuation and actual nonempty carriers. | active |
| T7 / I4 / P5 | Specification gate checks the wrong witness shape. Derive the property through Choice and definition. | Witness is a derivation; property and definition simulation checked. | active |
| T8 / P8 | Same-state erasure is insufficient. Construct concrete cross-theory simulations and finite composition. | Distinct base/extended proof systems and preserved old-language root. | active |
| T9 / P2 | Scope/history is partly structural. Preserve the proven structural results and track theory correspondence. | No state-lineage claim about MoonBit. | active |
| T10 / P9 / #15 | MoonBit refinement / provenance bug. | Deferred by explicit user instruction. | out of scope |
| T11 | Proof-status documentation must match theorem statements. | Build, axiom inspection and a reconciled status ledger. | typed core status recorded; full ledger active |

## Ordered work and verification

1. Build typed syntax and concrete interpretation; prove substitution lemmas locally. **Complete for the typed core.**
2. Prove exact rules and consistency by derivation induction. **Complete for the typed primitive core.**
3. Construct semantic extension contracts and concrete definitional proof translations.
4. Reconcile remaining correspondence and type-extension simulation obligations explicitly.
5. Run targeted Lean checks, project build and `#print axioms` on the main results;
   update the specification/audit ledger and existing PR.

The main risks are dependent transports under type instantiation and full syntactic
conservativity for type definitions. Model extension alone must never be called
syntactic conservativity: doing so would require a proved completeness theorem or
an explicit derivation translation.
