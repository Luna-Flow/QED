import QEDFV.HOL.DerivedRules
import QEDFV.HOL.TdLaws
import QEDFV.HOL.UnfoldBelow
import QEDFV.HOL.KernelState

/-! A constant specification is a definition by Hilbert choice.

The kernel's `ks_specify_const` publishes two theorems for a new constant `c` with predicate
`P` and witness `w`: the defining equation `c = ε P` and the property `P c`. The history
calculus has a dedicated `specification` step that publishes only `P c`. This file shows that
the kernel's form is the definition step `c := ε P` (`SpecificationExtension.asDefinition`):
the equation is that step's theorem, and `P c` follows from it and the witness by the
ordinary rules (`spec_of_definition`). So the kernel's specification is covered by the
definition gate, and the extra equation it publishes adds nothing beyond a definition. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ : List Ty} {a b : Ty}

/-- Constants of a substituted term come from the term or from the substituted values. -/
theorem Term.constIds_substitute_subset (C : Finset Nat) (t : Term S Γ a) (σ : Sub S Γ Δ)
    (hσ : ∀ {b} (v : Var Γ b), (σ v).constIds ⊆ C) :
    (t.substitute σ).constIds ⊆ t.constIds ∪ C := by
  induction t generalizing Δ with
  | var v => exact fun c hc ↦ Finset.mem_union_right _ (hσ v hc)
  | const c τ h => exact Finset.subset_union_left
  | app f x ihf ihx =>
      intro c hc
      simp only [Term.substitute, Term.constIds, Finset.mem_union] at hc ⊢
      rcases hc with hc | hc
      · rcases Finset.mem_union.mp (ihf σ hσ hc) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp (ihx σ hσ hc) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | lam p ih =>
      refine ih σ.lift (fun {b} v ↦ ?_)
      cases v with
      | zero => simp [Sub.lift, Term.constIds]
      | succ v => simp only [Sub.lift, Term.constIds_rename]; exact hσ v
  | truth => simp [Term.substitute, Term.constIds]
  | falsity => simp [Term.substitute, Term.constIds]
  | conj p q ihp ihq =>
      intro c hc
      simp only [Term.substitute, Term.constIds, Finset.mem_union] at hc ⊢
      rcases hc with hc | hc
      · rcases Finset.mem_union.mp (ihp σ hσ hc) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp (ihq σ hσ hc) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | imp p q ihp ihq =>
      intro c hc
      simp only [Term.substitute, Term.constIds, Finset.mem_union] at hc ⊢
      rcases hc with hc | hc
      · rcases Finset.mem_union.mp (ihp σ hσ hc) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp (ihq σ hσ hc) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | all p ih =>
      refine ih σ.lift (fun {b} v ↦ ?_)
      cases v with
      | zero => simp [Sub.lift, Term.constIds]
      | succ v => simp only [Sub.lift, Term.constIds_rename]; exact hσ v
  | ex p ih =>
      refine ih σ.lift (fun {b} v ↦ ?_)
      cases v with
      | zero => simp [Sub.lift, Term.constIds]
      | succ v => simp only [Sub.lift, Term.constIds_rename]; exact hσ v
  | eq => simp [Term.substitute, Term.constIds]
  | choice => simp [Term.substitute, Term.constIds]

theorem Term.constIds_substitute_single (p : Term S (a :: Γ) b) (w : Term S Γ a) :
    (p.substitute (Sub.single w)).constIds ⊆ p.constIds ∪ w.constIds :=
  p.constIds_substitute_subset w.constIds (Sub.single w) (fun {b} v ↦ by
    cases v with
    | zero => exact fun _ h ↦ h
    | succ v => simp [Sub.single, Term.constIds])

theorem Term.cast_const {τ τ' : Ty} (h : τ = τ') (c : Nat) (p : (S c).IsInst τ)
    (p' : (S c).IsInst τ') : (h ▸ (Term.const c τ p : Term S Γ τ)) = Term.const c τ' p' := by
  subst h; rfl

theorem Term.cast_cast_symm {a b : Ty} (h : a = b) (t : Term S Γ b) : h ▸ (h.symm ▸ t) = t := by
  subst h; rfl

namespace SpecificationExtension

/-- The definition `c := ε P` of a specified constant. -/
def asDefinition (E : SpecificationExtension S) : DefinitionGate S where
  id := E.gate.id
  rhs := E.typeEq.symm ▸ specificationTerm E.gate.predicate
  fresh := by
    rw [Term.constIds_cast]
    intro h
    apply E.gate.fresh
    simp only [specificationTerm, Term.constIds, Finset.mem_union, Finset.notMem_empty,
      false_or] at h
    exact Finset.mem_union_left _ h
  typeVarsClosed := by
    rw [Term.annotVars_cast, E.typeEq]
    intro i hi
    simp only [specificationTerm, Term.annotVars, Set.mem_union] at hi
    rcases hi with hi | hi | hi
    · simp only [Ty.typeVars, Set.mem_union] at hi
      rcases hi with (hi | hi) | hi <;> first | exact hi | simp at hi
    · exact hi
    · exact E.gate.typeVarsClosed hi

/-- The definition step publishes the kernel's choice equation `c = ε P`. -/
theorem choice_eq (E : SpecificationExtension S) {es : List (ModelExtension S)}
    (hFresh : E.gate.id ∉ modelHistoryIds es) :
    HistoryDerivation S (.definition E.asDefinition :: es)
      { hyps := [], concl :=
          (E.gate.constant E.typeEq).equal (specificationTerm E.gate.predicate) } := by
  have d := HistoryDerivation.cast_equal E.typeEq
    (HistoryDerivation.definition E.asDefinition hFresh)
  have h1 : (E.typeEq ▸ E.asDefinition.head) = E.gate.constant E.typeEq := by
    simp only [DefinitionGate.head, SpecificationGate.constant]
    exact Term.cast_const E.typeEq _ _ _
  have h2 : (E.typeEq ▸ E.asDefinition.rhs) = specificationTerm E.gate.predicate :=
    Term.cast_cast_symm E.typeEq _
  rw [h1, h2] at d
  exact d

/-- **The kernel's specification is a definition.** From a witness derived before the step,
the property `P c` is derivable after the definition `c := ε P`. -/
theorem spec_of_definition (E : SpecificationExtension S) {es : List (ModelExtension S)}
    (hFresh : E.gate.id ∉ modelHistoryIds es)
    (d : HistoryDerivation S es { hyps := [], concl := E.gate.body }) :
    HistoryDerivation S (.definition E.asDefinition :: es) (specSequent E) := by
  set P := E.gate.predicate
  set c := E.gate.constant E.typeEq
  have hOld : (ModelExtension.definition E.asDefinition).oldLanguage
      ({ hyps := [], concl := E.gate.body } : Sequent S []) := by
    intro h
    simp only [Sequent.constIds, List.foldr_nil, Finset.mem_union, Finset.notMem_empty,
      false_or, SpecificationGate.body] at h
    exact E.gate.fresh (Term.constIds_substitute_single _ _ h)
  have hw := HistoryDerivation.weaken (.definition E.asDefinition) d hOld
  have hε := HistoryDerivation.chooseHyp (A := { hyps := [], concl := E.gate.body })
    P E.gate.witness rfl hw
  have heq := choice_eq E hFresh
  have h4 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (L := []) (Term.lam P)) heq
  have bc : HistoryDerivation S (.definition E.asDefinition :: es)
      { hyps := [], concl := ((Term.lam P).app c).equal (P.substitute (Sub.single c)) } :=
    .core (.beta P c)
  have be : HistoryDerivation S (.definition E.asDefinition :: es)
      { hyps := [], concl := ((Term.lam P).app (specificationTerm P)).equal
          (P.substitute (Sub.single (specificationTerm P))) } :=
    .core (.beta P (specificationTerm P))
  have h5 := HistoryDerivation.trans' (HistoryDerivation.sym bc)
    (HistoryDerivation.trans' h4 be)
  exact HistoryDerivation.eqMp' (HistoryDerivation.sym h5) hε

end SpecificationExtension

end QEDFV.HOL
