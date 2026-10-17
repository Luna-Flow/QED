import QEDFV.HOL.Unfold

/-! Syntactic erasure of a specification step: the specified constant is replaced by the
Hilbert-choice term of its predicate. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ : List Ty} {a b : Ty}

/-- The closed choice term `ε (λx. P)` of a specification, at the instance `σ`. -/
def SpecificationExtension.choiceAt (E : SpecificationExtension S) (σ : TypeSub) :
    Term S [] (E.gate.ty.subst σ) :=
  Term.choice.app ((Term.lam E.gate.predicate).instType σ)

/-- Replacement unfolding a specification: the specified constant at instance `σ` becomes the
choice term of the predicate instantiated at `σ`; every other constant stays. -/
def SpecificationExtension.repl (E : SpecificationExtension S) : ConstRepl S := fun c σ ↦
  if h : c = E.gate.id then
    (congrArg (Ty.subst σ) ((congrArg S h).trans E.typeEq)).symm ▸ E.choiceAt σ
  else Term.const c σ

theorem SpecificationExtension.repl_compatible (E : SpecificationExtension S) :
    E.repl.Compatible := by
  intro c θ σ
  by_cases h : c = E.gate.id
  · simp only [SpecificationExtension.repl, h, dite_true]
    apply Term.erase_inj
    rw [Term.erase_cast, Term.erase_instType, Term.erase_cast, Term.erase_cast]
    simp [SpecificationExtension.choiceAt, Term.erase, UTerm.inst, Term.erase_instType,
      UTerm.inst_comp, Ty.subst]
  · simp [SpecificationExtension.repl, h, Term.instType]

theorem SpecificationExtension.replConst_of_not_mem (E : SpecificationExtension S)
    (t : Term S Γ a) (h : E.gate.id ∉ t.constIds) : t.replConst E.repl = t := by
  induction t with
  | var v => rfl
  | const c σ =>
      have hne : c ≠ E.gate.id := fun e ↦ h (by simp [Term.constIds, e])
      simp [Term.replConst, SpecificationExtension.repl, hne, Term.closedLift, Term.rename]
  | app f x ihf ihx =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihf h.1, ihx h.2]
  | lam b ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihp h.1, ihq h.2]
  | imp p q ihp ihq =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihp h.1, ihq h.2]
  | all p ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | ex p ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | eq => rfl
  | choice => rfl

theorem SpecificationExtension.replConst_seq_of_not_mem (E : SpecificationExtension S)
    (s : Sequent S Γ) (h : E.gate.id ∉ s.constIds) : s.replConst E.repl = s := by
  cases s with
  | mk hyps concl =>
      have hh : ∀ x ∈ hyps, E.gate.id ∉ x.constIds := fun x hx hm ↦
        h (Sequent.mem_constIds_hyp (s := { hyps := hyps, concl := concl }) hx hm)
      have hc : E.gate.id ∉ concl.constIds := fun hm ↦
        h (Sequent.mem_constIds_concl (s := { hyps := hyps, concl := concl }) hm)
      simp only [Sequent.replConst]
      rw [E.replConst_of_not_mem concl hc]
      congr 1
      rw [List.map_congr_left (fun x hx ↦ E.replConst_of_not_mem x (hh x hx))]
      simp

/-- Unfolding the specified constant gives its choice term. -/
theorem SpecificationExtension.replConst_constant (E : SpecificationExtension S) :
    (E.gate.constant E.typeEq).replConst E.repl = specificationTerm E.gate.predicate := by
  unfold SpecificationGate.constant
  simp only []
  rw [Term.replConst_cast]
  simp only [Term.replConst, SpecificationExtension.repl, dite_true]
  rw [Term.closedLift_nil]
  apply Term.erase_inj
  simp [Term.erase_cast, SpecificationExtension.choiceAt, specificationTerm, Term.erase,
    Term.erase_instType, UTerm.inst_var]

/-- The replaced conclusion of a specification step is derivable from the witness
derivation: the replaced predicate is the predicate itself, and the replaced constant is the
choice term. -/
theorem SpecificationExtension.erase_conclusion (E : SpecificationExtension S)
    {es : List (ModelExtension S)}
    (d : HistoryDerivation S es { hyps := [], concl := E.gate.body }) :
    HistoryDerivation S es
      (({ hyps := [], concl := E.gate.predicate.substitute
            (Sub.single (E.gate.constant E.typeEq)) } : Sequent S []).replConst E.repl) := by
  have hp : E.gate.id ∉ E.gate.predicate.constIds := fun h ↦
    E.gate.fresh (Finset.mem_union_left _ h)
  refine HistoryDerivation.of_eq ?_ (.chooseWitness E.gate.predicate E.gate.witness d)
  simp only [Sequent.replConst, List.map_nil]
  rw [Term.replConst_single, E.replConst_of_not_mem _ hp, E.replConst_constant]
  rfl

theorem ExtensionDerivation.erase_specification_aux (E : SpecificationExtension S)
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) :
    ∀ es, h = ModelExtension.specification E :: es →
      HistoryDerivation S es (s.replConst E.repl) := by
  induction d with
  | core d => exact fun es _ ↦ Derivation.replConst E.repl E.repl_compatible es d
  | weaken e d hOld ih =>
      intro es heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hOld' : E.gate.id ∉ _ := hOld
      rw [E.replConst_seq_of_not_mem _ hOld']
      exact .extension d
  | definition D hFresh => intro es heq; cases heq
  | specification E' hFresh d ih =>
      intro es heq
      obtain ⟨hE, rfl⟩ := List.cons.inj heq
      cases hE
      exact E.erase_conclusion (.extension d)
  | typedef G l hk hrep habs w d ih => intro es heq; cases heq

theorem HistoryDerivation.erase_specification_aux (E : SpecificationExtension S)
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) :
    ∀ es, h = ModelExtension.specification E :: es →
      HistoryDerivation S es (s.replConst E.repl) := by
  induction d with
  | core d => exact fun es _ ↦ Derivation.replConst E.repl E.repl_compatible es d
  | extension d => exact fun es heq ↦ ExtensionDerivation.erase_specification_aux E d es heq
  | weaken e d hOld ih =>
      intro es heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hOld' : E.gate.id ∉ _ := hOld
      rw [E.replConst_seq_of_not_mem _ hOld']
      exact d
  | definition D hFresh => intro es heq; cases heq
  | specification E' hFresh d ih =>
      intro es heq
      obtain ⟨hE, rfl⟩ := List.cons.inj heq
      cases hE
      exact E.erase_conclusion d
  | typedef G l hk hrep habs w d ih => intro es heq; cases heq
  | addAssum p d ih => exact fun es heq ↦ replConst_step_addAssum E.repl p (ih es heq)
  | weakenHyps L hL d ih => exact fun es heq ↦ replConst_step_weakenHyps E.repl L hL (ih es heq)
  | trans hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_trans E.repl hA hB (ihA es heq) (ihB es heq)
  | mkComb hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_mkComb E.repl hA hB (ihA es heq) (ihB es heq)
  | abs d ih => exact fun es heq ↦ replConst_step_abs E.repl (ih es heq)
  | eqMp hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_eqMp E.repl hA hB (ihA es heq) (ihB es heq)
  | deduct dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_deduct E.repl (ihA es heq) (ihB es heq)
  | instType θ d ih =>
      exact fun es heq ↦ replConst_step_instType E.repl E.repl_compatible θ (ih es heq)
  | instTerm σ d ih => exact fun es heq ↦ replConst_step_instTerm E.repl σ (ih es heq)
  | chooseWitness p w d ih =>
      exact fun es heq ↦ replConst_step_chooseWitness E.repl p w (ih es heq)

/-- **Specification erasure.** A derivation at the history `specification E :: es` yields a
derivation at `es` of the sequent in which the specified constant is replaced by the choice
term of its predicate. -/
theorem HistoryDerivation.erase_specification (E : SpecificationExtension S)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (.specification E :: es) s) :
    HistoryDerivation S es (s.replConst E.repl) :=
  HistoryDerivation.erase_specification_aux E d es rfl

/-- **Syntactic conservativity of a specification.** A sequent that does not mention the
specified constant and is derivable after the specification is derivable before it. -/
theorem HistoryDerivation.specification_conservative (E : SpecificationExtension S)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (.specification E :: es) s) (hOld : E.gate.id ∉ s.constIds) :
    HistoryDerivation S es s := by
  have := d.erase_specification E
  rwa [E.replConst_seq_of_not_mem s hOld] at this

end QEDFV.HOL
