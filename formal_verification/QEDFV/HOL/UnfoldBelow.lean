import QEDFV.HOL.SpecErasure

/-! Constants, type constructors and annotation variables of a term after replacing its
constants. Used to rewrite the gate of a declaration that sits above the replaced step. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ : List Ty} {a b : Ty}

theorem Term.annotVars_rename (t : Term S Γ a) (r : Ren Γ Δ) :
    (t.rename r).annotVars = t.annotVars := by
  induction t generalizing Δ with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [Term.rename, Term.annotVars, ihf, ihx]
  | lam b ih => simp only [Term.rename, Term.annotVars, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.annotVars, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.annotVars, ihp, ihq]
  | all p ih => simp only [Term.rename, Term.annotVars, ih]
  | ex p ih => simp only [Term.rename, Term.annotVars, ih]
  | eq => rfl
  | choice => rfl

theorem Term.tyCons_rename (t : Term S Γ a) (r : Ren Γ Δ) :
    (t.rename r).tyCons = t.tyCons := by
  induction t generalizing Δ with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [Term.rename, Term.tyCons, ihf, ihx]
  | lam b ih => simp only [Term.rename, Term.tyCons, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.tyCons, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.tyCons, ihp, ihq]
  | all p ih => simp only [Term.rename, Term.tyCons, ih]
  | ex p ih => simp only [Term.rename, Term.tyCons, ih]
  | eq => rfl
  | choice => rfl

theorem Term.constIds_rename (t : Term S Γ a) (r : Ren Γ Δ) :
    (t.rename r).constIds = t.constIds := by
  induction t generalizing Δ with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [Term.rename, Term.constIds, ihf, ihx]
  | lam b ih => simp only [Term.rename, Term.constIds, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.constIds, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.constIds, ihp, ihq]
  | all p ih => simp only [Term.rename, Term.constIds, ih]
  | ex p ih => simp only [Term.rename, Term.constIds, ih]
  | eq => rfl
  | choice => rfl

theorem Term.constIds_instType (t : Term S Γ a) (θ : TypeSub) :
    (t.instType θ).constIds = t.constIds := by
  induction t with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [Term.instType, Term.constIds, ihf, ihx]
  | lam b ih => simp only [Term.instType, Term.constIds, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.instType, Term.constIds, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.instType, Term.constIds, ihp, ihq]
  | all p ih => simp only [Term.instType, Term.constIds, ih]
  | ex p ih => simp only [Term.instType, Term.constIds, ih]
  | eq => rfl
  | choice => rfl

theorem Term.annotVars_instType (t : Term S Γ a) (θ : TypeSub) :
    (t.instType θ).annotVars = TypeSub.imageTypeVars θ t.annotVars := by
  induction t with
  | var v => simp [Term.instType, Term.annotVars, Ty.typeVars_subst, TypeSub.imageTypeVars]
  | const c τ h =>
      simp only [Term.instType, Term.annotVars, Ty.typeVars_subst]
  | app f x ihf ihx =>
      simp only [Term.instType, Term.annotVars, ihf, ihx, TypeSub.imageTypeVars_union]
  | lam b ih =>
      simp only [Term.instType, Term.annotVars, ih, Ty.typeVars_subst, TypeSub.imageTypeVars_union]
  | truth => simp [Term.instType, Term.annotVars, TypeSub.imageTypeVars]
  | falsity => simp [Term.instType, Term.annotVars, TypeSub.imageTypeVars]
  | conj p q ihp ihq =>
      simp only [Term.instType, Term.annotVars, ihp, ihq, TypeSub.imageTypeVars_union]
  | imp p q ihp ihq =>
      simp only [Term.instType, Term.annotVars, ihp, ihq, TypeSub.imageTypeVars_union]
  | all p ih =>
      simp only [Term.instType, Term.annotVars, ih, Ty.typeVars_subst, TypeSub.imageTypeVars_union]
  | ex p ih =>
      simp only [Term.instType, Term.annotVars, ih, Ty.typeVars_subst, TypeSub.imageTypeVars_union]
  | eq => simp [Term.instType, Term.annotVars, Ty.typeVars, TypeSub.imageTypeVars, Ty.typeVars_subst]
  | choice => simp [Term.instType, Term.annotVars, Ty.typeVars, TypeSub.imageTypeVars, Ty.typeVars_subst]

theorem Term.annotVars_closedLift (t : Term S [] a) :
    (t.closedLift : Term S Γ a).annotVars = t.annotVars := Term.annotVars_rename _ _

theorem Term.tyCons_closedLift (t : Term S [] a) :
    (t.closedLift : Term S Γ a).tyCons = t.tyCons := Term.tyCons_rename _ _

theorem Term.constIds_closedLift (t : Term S [] a) :
    (t.closedLift : Term S Γ a).constIds = t.constIds := Term.constIds_rename _ _

section Bounds

variable (R : ConstRepl S)

theorem Term.annotVars_replConst_subset
    (hA : ∀ c τ (h : (S c).IsInst τ), (R c τ h).annotVars ⊆ τ.typeVars) (t : Term S Γ a) :
    (t.replConst R).annotVars ⊆ t.annotVars := by
  induction t with
  | var v => exact subset_rfl
  | const c τ h =>
      simp only [Term.replConst, Term.annotVars, Term.annotVars_closedLift]
      exact hA c τ h
  | app f x ihf ihx =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union ihf ihx
  | lam b ih =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union subset_rfl ih
  | truth => exact subset_rfl
  | falsity => exact subset_rfl
  | conj p q ihp ihq =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union ihp ihq
  | imp p q ihp ihq =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union ihp ihq
  | all p ih =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union subset_rfl ih
  | ex p ih =>
      simp only [Term.replConst, Term.annotVars]
      exact Set.union_subset_union subset_rfl ih
  | eq => exact subset_rfl
  | choice => exact subset_rfl

theorem Term.tyCons_replConst_subset (T0 : Set Nat)
    (hT : ∀ c τ (h : (S c).IsInst τ), (R c τ h).tyCons ⊆ τ.tyCons ∪ T0) (t : Term S Γ a) :
    (t.replConst R).tyCons ⊆ t.tyCons ∪ T0 := by
  induction t with
  | var v => exact Set.subset_union_of_subset_left subset_rfl _
  | const c τ h =>
      simp only [Term.replConst, Term.tyCons, Term.tyCons_closedLift]
      exact hT c τ h
  | app f x ihf ihx =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · rcases ihf hk with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihx hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | lam b ih =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · exact Or.inl (Or.inl hk)
      · rcases ih hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | truth => exact Set.subset_union_of_subset_left subset_rfl _
  | falsity => exact Set.subset_union_of_subset_left subset_rfl _
  | conj p q ihp ihq =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · rcases ihp hk with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihq hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | imp p q ihp ihq =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · rcases ihp hk with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihq hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | all p ih =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · exact Or.inl (Or.inl hk)
      · rcases ih hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | ex p ih =>
      simp only [Term.replConst, Term.tyCons]
      intro k hk
      rcases hk with hk | hk
      · exact Or.inl (Or.inl hk)
      · rcases ih hk with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | eq => exact Set.subset_union_of_subset_left subset_rfl _
  | choice => exact Set.subset_union_of_subset_left subset_rfl _

theorem Term.constIds_replConst_subset (C0 : Finset Nat)
    (hC : ∀ c τ (h : (S c).IsInst τ), (R c τ h).constIds ⊆ {c} ∪ C0) (t : Term S Γ a) :
    (t.replConst R).constIds ⊆ t.constIds ∪ C0 := by
  classical
  induction t with
  | var v => simp [Term.replConst, Term.constIds]
  | const c τ h =>
      simp only [Term.replConst, Term.constIds, Term.constIds_closedLift]
      exact hC c τ h
  | app f x ihf ihx =>
      simp only [Term.replConst, Term.constIds]
      intro k hk
      rw [Finset.mem_union] at hk
      rcases hk with hk | hk
      · have := ihf hk
        simp only [Finset.mem_union] at this ⊢
        tauto
      · have := ihx hk
        simp only [Finset.mem_union] at this ⊢
        tauto
  | lam b ih => simpa only [Term.replConst, Term.constIds] using ih
  | truth => simp [Term.replConst, Term.constIds]
  | falsity => simp [Term.replConst, Term.constIds]
  | conj p q ihp ihq =>
      simp only [Term.replConst, Term.constIds]
      intro k hk
      rw [Finset.mem_union] at hk
      rcases hk with hk | hk
      · have := ihp hk
        simp only [Finset.mem_union] at this ⊢
        tauto
      · have := ihq hk
        simp only [Finset.mem_union] at this ⊢
        tauto
  | imp p q ihp ihq =>
      simp only [Term.replConst, Term.constIds]
      intro k hk
      rw [Finset.mem_union] at hk
      rcases hk with hk | hk
      · have := ihp hk
        simp only [Finset.mem_union] at this ⊢
        tauto
      · have := ihq hk
        simp only [Finset.mem_union] at this ⊢
        tauto
  | all p ih => simpa only [Term.replConst, Term.constIds] using ih
  | ex p ih => simpa only [Term.replConst, Term.constIds] using ih
  | eq => simp [Term.replConst, Term.constIds]
  | choice => simp [Term.replConst, Term.constIds]

end Bounds

theorem Term.annotVars_cast {h : a = b} (t : Term S Γ a) :
    (h ▸ t).annotVars = t.annotVars := by
  cases h
  rfl

theorem Term.constIds_cast {h : a = b} (t : Term S Γ a) :
    (h ▸ t).constIds = t.constIds := by
  cases h
  rfl

section DefBounds

variable (D : DefinitionGate S)

theorem DefinitionGate.repl_annotVars (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (D.repl c τ h).annotVars ⊆ τ.typeVars := by
  by_cases hc : c = D.id
  · subst hc
    simp only [DefinitionGate.repl, dite_true]
    rw [Term.annotVars_cast, Term.annotVars_instType]
    intro i hi
    obtain ⟨j, hj, hi⟩ := hi
    have hj' : j ∈ (S D.id).typeVars := D.typeVarsClosed hj
    rw [← Ty.constSub_spec (S D.id) τ h, Ty.typeVars_subst]
    exact ⟨j, hj', hi⟩
  · simp [DefinitionGate.repl, hc, Term.annotVars]

theorem DefinitionGate.repl_tyCons (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (D.repl c τ h).tyCons ⊆ τ.tyCons ∪ D.rhs.tyCons := by
  by_cases hc : c = D.id
  · subst hc
    simp only [DefinitionGate.repl, dite_true]
    rw [Term.tyCons_cast, Term.tyCons_instType]
    intro k hk
    rcases hk with hk | ⟨j, hj, hk⟩
    · exact Or.inr hk
    · left
      have hj' : j ∈ (S D.id).typeVars := D.typeVarsClosed hj
      rw [← Ty.constSub_spec (S D.id) τ h, Ty.tyCons_subst]
      exact Or.inr ⟨j, hj', hk⟩
  · simp [DefinitionGate.repl, hc, Term.tyCons]

theorem DefinitionGate.repl_constIds (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (D.repl c τ h).constIds ⊆ {c} ∪ D.rhs.constIds := by
  by_cases hc : c = D.id
  · subst hc
    simp only [DefinitionGate.repl, dite_true]
    rw [Term.constIds_cast, Term.constIds_instType]
    exact Finset.subset_union_right
  · simp [DefinitionGate.repl, hc, Term.constIds]

end DefBounds

section SpecBounds

variable (E : SpecificationExtension S)

theorem SpecificationExtension.repl_annotVars (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (E.repl c τ h).annotVars ⊆ τ.typeVars := by
  by_cases hc : c = E.gate.id
  · subst hc
    simp only [SpecificationExtension.repl, dite_true]
    rw [Term.annotVars_cast]
    have e := E.instTy_eq h
    intro i hi
    simp only [SpecificationExtension.choiceAt, Term.annotVars, Term.annotVars_instType,
      Set.mem_union] at hi
    rw [← e]
    rcases hi with hi | ⟨j, hj, hi⟩
    · simpa [Ty.typeVars] using hi
    · simp only [Term.annotVars, Set.mem_union] at hj
      rw [Ty.typeVars_subst]
      refine ⟨j, ?_, hi⟩
      rcases hj with hj | hj
      · exact hj
      · exact E.gate.typeVarsClosed hj
  · simp [SpecificationExtension.repl, hc, Term.annotVars]

theorem SpecificationExtension.repl_tyCons (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (E.repl c τ h).tyCons ⊆ τ.tyCons ∪ E.gate.predicate.tyCons := by
  by_cases hc : c = E.gate.id
  · subst hc
    simp only [SpecificationExtension.repl, dite_true]
    rw [Term.tyCons_cast]
    have e := E.instTy_eq h
    intro k hk
    simp only [SpecificationExtension.choiceAt, Term.tyCons, Term.tyCons_instType,
      Set.mem_union] at hk
    rw [← e]
    rcases hk with hk | hk | ⟨j, hj, hk⟩
    · left; simpa [Ty.tyCons] using hk
    · rcases hk with hk | hk
      · left
        rw [Ty.tyCons_subst]
        exact Or.inl hk
      · right; exact hk
    · left
      rw [Ty.tyCons_subst]
      refine Or.inr ⟨j, ?_, hk⟩
      simp only [Term.annotVars, Set.mem_union] at hj
      rcases hj with hj | hj
      · exact hj
      · exact E.gate.typeVarsClosed hj
  · simp [SpecificationExtension.repl, hc, Term.tyCons]

theorem SpecificationExtension.repl_constIds (c : Nat) (τ : Ty) (h : (S c).IsInst τ) :
    (E.repl c τ h).constIds ⊆ {c} ∪ E.gate.predicate.constIds := by
  by_cases hc : c = E.gate.id
  · subst hc
    simp only [SpecificationExtension.repl, dite_true]
    rw [Term.constIds_cast]
    simp only [SpecificationExtension.choiceAt, Term.constIds, Term.constIds_instType]
    intro x hx
    simp only [Finset.mem_union, Finset.notMem_empty, false_or] at hx ⊢
    exact Or.inr hx
  · simp [SpecificationExtension.repl, hc, Term.constIds]

end SpecBounds

/-! ### Unfolding a declaration below a type definition -/

/-- An unfolding of a declaration step: a compatible replacement with bounds on what it
introduces, the erasure of the step from derivations, and the fact that a term not mentioning
the declared constant is unchanged. -/
structure Unfolder (S : Signature) where
  step : ModelExtension S
  R : ConstRepl S
  compat : R.Compatible
  id : Nat
  T0 : Set Nat
  C0 : Finset Nat
  annot : ∀ c τ (h : (S c).IsInst τ), (R c τ h).annotVars ⊆ τ.typeVars
  tyC : ∀ c τ (h : (S c).IsInst τ), (R c τ h).tyCons ⊆ τ.tyCons ∪ T0
  constI : ∀ c τ (h : (S c).IsInst τ), (R c τ h).constIds ⊆ {c} ∪ C0
  fixes : ∀ {Γ : List Ty} {a : Ty} (t : Term S Γ a), id ∉ t.constIds → t.replConst R = t
  erase : ∀ {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ},
    HistoryDerivation S (step :: es) s → HistoryDerivation S es (s.replConst R)

/-- The unfolded declaration does not mention the type definition's symbols. -/
structure Unfolder.Below (U : Unfolder S) (G : TypeDefGate S) : Prop where
  k_fresh : G.k ∉ U.T0
  rep_fresh : G.rep ∉ U.C0
  abs_fresh : G.abs ∉ U.C0
  id_ne_rep : U.id ≠ G.rep
  id_ne_abs : U.id ≠ G.abs

noncomputable def DefinitionGate.unfolder (D : DefinitionGate S) : Unfolder S where
  step := .definition D
  R := D.repl
  compat := D.repl_compatible
  id := D.id
  T0 := D.rhs.tyCons
  C0 := D.rhs.constIds
  annot := D.repl_annotVars
  tyC := D.repl_tyCons
  constI := D.repl_constIds
  fixes := fun t h ↦ D.replConst_of_not_mem t h
  erase := fun d ↦ HistoryDerivation.erase_definition D d

noncomputable def SpecificationExtension.unfolder (E : SpecificationExtension S) : Unfolder S where
  step := .specification E
  R := E.repl
  compat := E.repl_compatible
  id := E.gate.id
  T0 := E.gate.predicate.tyCons
  C0 := E.gate.predicate.constIds
  annot := E.repl_annotVars
  tyC := E.repl_tyCons
  constI := E.repl_constIds
  fixes := fun t h ↦ E.replConst_of_not_mem t h
  erase := fun d ↦ HistoryDerivation.erase_specification E d

/-- The type definition with a declaration below it unfolded in its predicate. -/
noncomputable def TypeDefGate.unfold (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) : TypeDefGate S where
  k := G.k
  n := G.n
  repTy := G.repTy
  pred := G.pred.replConst U.R
  rep := G.rep
  abs := G.abs
  rep_ty := G.rep_ty
  abs_ty := G.abs_ty
  closed := fun i hi ↦
    G.closed i (Term.annotVars_replConst_subset U.R U.annot G.pred hi)
  k_fresh := fun hk ↦ by
    rcases Term.tyCons_replConst_subset U.R U.T0 U.tyC G.pred hk with h | h
    · exact G.k_fresh h
    · exact hB.k_fresh h
  rep_ne_abs := G.rep_ne_abs
  rep_fresh := fun hk ↦ by
    rcases Finset.mem_union.1 (Term.constIds_replConst_subset U.R U.C0 U.constI G.pred hk) with h | h
    · exact G.rep_fresh h
    · exact hB.rep_fresh h
  abs_fresh := fun hk ↦ by
    rcases Finset.mem_union.1 (Term.constIds_replConst_subset U.R U.C0 U.constI G.pred hk) with h | h
    · exact G.abs_fresh h
    · exact hB.abs_fresh h

theorem Sequent.tyCons_replConst_subset (R : ConstRepl S) (T0 : Set Nat)
    (hT : ∀ c τ (h : (S c).IsInst τ), (R c τ h).tyCons ⊆ τ.tyCons ∪ T0) (s : Sequent S Γ) :
    (s.replConst R).tyCons ⊆ s.tyCons ∪ T0 := by
  intro k hk
  rcases hk with ⟨h, hh, hk⟩ | hk
  · simp only [Sequent.replConst, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    rcases Term.tyCons_replConst_subset R T0 hT h0 hk with h | h
    · exact Or.inl (Or.inl ⟨h0, hh0, h⟩)
    · exact Or.inr h
  · rcases Term.tyCons_replConst_subset R T0 hT s.concl hk with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem Sequent.constIds_replConst_subset (R : ConstRepl S) (C0 : Finset Nat)
    (hC : ∀ c τ (h : (S c).IsInst τ), (R c τ h).constIds ⊆ {c} ∪ C0) (s : Sequent S Γ) :
    (s.replConst R).constIds ⊆ s.constIds ∪ C0 := by
  classical
  intro c hc
  simp only [Sequent.constIds, Finset.mem_union] at hc ⊢
  rcases hc with hc | hc
  · have hmem : ∀ (hs : List (Term S Γ .bool)),
        c ∈ (hs.map (Term.replConst R)).foldr (fun h acc ↦ h.constIds ∪ acc) ∅ →
        c ∈ hs.foldr (fun h acc ↦ h.constIds ∪ acc) ∅ ∨ c ∈ C0 := by
      intro hs
      induction hs with
      | nil => intro h; simp at h
      | cons x xs ih =>
          intro h
          simp only [List.map_cons, List.foldr_cons, Finset.mem_union] at h ⊢
          rcases h with h | h
          · have := Term.constIds_replConst_subset R C0 hC x h
            simp only [Finset.mem_union] at this
            tauto
          · have := ih h
            tauto
    simp only [Sequent.replConst] at hc
    rcases hmem s.hyps hc with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · have := Term.constIds_replConst_subset R C0 hC s.concl hc
    simp only [Finset.mem_union] at this
    simp only [Sequent.replConst] at hc
    tauto

theorem TypeDefGate.unfold_oldLanguage (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) {s : Sequent S Γ}
    (h : (ModelExtension.typeDefinition G).oldLanguage s) :
    (ModelExtension.typeDefinition (G.unfold U hB)).oldLanguage (s.replConst U.R) := by
  obtain ⟨hk, hr, ha⟩ := h
  refine ⟨fun hk' ↦ ?_, fun hr' ↦ ?_, fun ha' ↦ ?_⟩
  · rcases Sequent.tyCons_replConst_subset U.R U.T0 U.tyC s hk' with h | h
    · exact hk h
    · exact hB.k_fresh h
  · rcases Finset.mem_union.1 (Sequent.constIds_replConst_subset U.R U.C0 U.constI s hr') with h | h
    · exact hr h
    · exact hB.rep_fresh h
  · rcases Finset.mem_union.1 (Sequent.constIds_replConst_subset U.R U.C0 U.constI s ha') with h | h
    · exact ha h
    · exact hB.abs_fresh h

theorem TypeDefGate.unfold_repTerm (G : TypeDefGate S) (U : Unfolder S) (hB : U.Below G)
    {Γ : List Ty} : (G.repTerm (Γ := Γ)).replConst U.R = G.repTerm := by
  apply U.fixes
  simp only [TypeDefGate.repTerm, Term.constIds, Finset.mem_singleton]
  exact hB.id_ne_rep

theorem TypeDefGate.unfold_absTerm (G : TypeDefGate S) (U : Unfolder S) (hB : U.Below G)
    {Γ : List Ty} : (G.absTerm (Γ := Γ)).replConst U.R = G.absTerm := by
  apply U.fixes
  simp only [TypeDefGate.absTerm, Term.constIds, Finset.mem_singleton]
  exact hB.id_ne_abs

theorem TypeDefGate.unfold_predIn (G : TypeDefGate S) (U : Unfolder S) (hB : U.Below G)
    (Γ : List Ty) : (G.predIn Γ).replConst U.R = (G.unfold U hB).predIn Γ := by
  unfold TypeDefGate.predIn
  rw [Term.replConst_rename]
  rfl

theorem TypeDefGate.unfold_law (G : TypeDefGate S) (U : Unfolder S) (hB : U.Below G)
    (l : TypeDefLaw) :
    (l.sequent G).replConst U.R = (l.sequent (G.unfold U hB)) := by
  cases l with
  | absRep =>
      change Sequent.replConst U.R (Sequent.mk [] ((G.absTerm.app (G.repTerm.app (Term.var Var.zero))).equal (Term.var Var.zero))) = _
      simp only [Sequent.replConst, List.map_nil, Term.replConst_equal, Term.replConst,
        G.unfold_absTerm U hB, G.unfold_repTerm U hB]
      rfl
  | repRange =>
      change Sequent.replConst U.R (Sequent.mk [] ((G.predIn [G.newTy]).app (G.repTerm.app (Term.var Var.zero)))) = _
      simp only [Sequent.replConst, List.map_nil, Term.replConst, G.unfold_predIn U hB,
        G.unfold_repTerm U hB]
      rfl
  | repAbs =>
      change Sequent.replConst U.R (Sequent.mk [(G.predIn [G.repTy]).app (Term.var Var.zero)] ((G.repTerm.app (G.absTerm.app (Term.var Var.zero))).equal (Term.var Var.zero))) = _
      simp only [Sequent.replConst, List.map_cons, List.map_nil, Term.replConst_equal,
        Term.replConst, G.unfold_predIn U hB, G.unfold_absTerm U hB, G.unfold_repTerm U hB]
      rfl

/-! ### Erasing a declaration below the head type definition -/

theorem typedef_hist_ids_tail {es0 : List (ModelExtension S)} {e : ModelExtension S} {n : Nat}
    (h : n ∉ modelHistoryIds (e :: es0)) : n ∉ modelHistoryIds es0 := by
  intro hm
  apply h
  simp only [modelHistoryIds, List.foldr_cons, Finset.mem_union]
  exact Or.inr hm

theorem typedef_hist_tyCons_tail {es0 : List (ModelExtension S)} {e : ModelExtension S} {k : Nat}
    (h : k ∉ modelHistoryTyCons (e :: es0)) : k ∉ modelHistoryTyCons es0 := by
  rintro ⟨e', he, hk⟩
  exact h ⟨e', List.mem_cons_of_mem _ he, hk⟩

theorem HistoryDerivation.erase_below_typedef (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) {es0 : List (ModelExtension S)} {l : TypeDefLaw} {w : Term S [] G.repTy}
    (hk : G.k ∉ modelHistoryTyCons (U.step :: es0))
    (hrep : G.rep ∉ modelHistoryIds (U.step :: es0))
    (habs : G.abs ∉ modelHistoryIds (U.step :: es0))
    (d : HistoryDerivation S (U.step :: es0) { hyps := [], concl := G.pred.app w }) :
    HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hB) :: es0)
      ((l.sequent G).replConst U.R) := by
  rw [G.unfold_law U hB l]
  exact .typedef (G.unfold U hB) l (typedef_hist_tyCons_tail hk) (typedef_hist_ids_tail hrep)
    (typedef_hist_ids_tail habs) (w.replConst U.R) (U.erase d)

theorem ExtensionDerivation.erase_below_aux (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) :
    ∀ es0, h = ModelExtension.typeDefinition G :: U.step :: es0 →
      HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hB) :: es0)
        (s.replConst U.R) := by
  induction d with
  | core d => exact fun es0 _ ↦ Derivation.replConst U.R U.compat _ d
  | weaken e d hOld ih =>
      intro es0 heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact .weaken _ (U.erase (.extension d)) (G.unfold_oldLanguage U hB hOld)
  | definition D' hFresh => intro es0 heq; cases heq
  | specification E hFresh d ih => intro es0 heq; cases heq
  | typedef G' l hk hrep habs w d ih =>
      intro es0 heq
      obtain ⟨hG, rfl⟩ := List.cons.inj heq
      cases hG
      exact HistoryDerivation.erase_below_typedef G U hB hk hrep habs (.extension d)



theorem HistoryDerivation.erase_below_aux (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) :
    ∀ es0, h = ModelExtension.typeDefinition G :: U.step :: es0 →
      HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hB) :: es0)
        (s.replConst U.R) := by
  induction d with
  | core d => exact fun es0 _ ↦ Derivation.replConst U.R U.compat _ d
  | extension d => exact fun es0 heq ↦ ExtensionDerivation.erase_below_aux G U hB d es0 heq
  | weaken e d hOld ih =>
      intro es0 heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact .weaken _ (U.erase d) (G.unfold_oldLanguage U hB hOld)
  | definition D' hFresh => intro es0 heq; cases heq
  | specification E hFresh d ih => intro es0 heq; cases heq
  | typedef G' l hk hrep habs w d ih =>
      intro es0 heq
      obtain ⟨hG, rfl⟩ := List.cons.inj heq
      cases hG
      exact HistoryDerivation.erase_below_typedef G U hB hk hrep habs d
  | addAssum p d ih => exact fun es0 heq ↦ replConst_step_addAssum U.R p (ih es0 heq)
  | weakenHyps L hL d ih => exact fun es0 heq ↦ replConst_step_weakenHyps U.R L hL (ih es0 heq)
  | trans hA hB dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_trans U.R hA hB (ihA es0 heq) (ihB es0 heq)
  | mkComb hA hB dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_mkComb U.R hA hB (ihA es0 heq) (ihB es0 heq)
  | abs d ih => exact fun es0 heq ↦ replConst_step_abs U.R (ih es0 heq)
  | eqMp hA hB dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_eqMp U.R hA hB (ihA es0 heq) (ihB es0 heq)
  | deduct dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_deduct U.R (ihA es0 heq) (ihB es0 heq)
  | instType θ d ih =>
      exact fun es0 heq ↦ replConst_step_instType U.R U.compat θ (ih es0 heq)
  | instTerm σ d ih => exact fun es0 heq ↦ replConst_step_instTerm U.R σ (ih es0 heq)
  | chooseWitness p w d ih =>
      exact fun es0 heq ↦ replConst_step_chooseWitness U.R p w (ih es0 heq)
  | truthIntro => exact fun es0 heq ↦ HistoryDerivation.of_eq rfl .truthIntro
  | falsityElim q hA d ih => exact fun es0 heq ↦ replConst_step_falsityElim U.R q hA (ih es0 heq)
  | conjIntro hA hB dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_conjIntro U.R hA hB (ihA es0 heq) (ihB es0 heq)
  | conjElimLeft hA d ih => exact fun es0 heq ↦ replConst_step_conjElimLeft U.R hA (ih es0 heq)
  | conjElimRight hA d ih => exact fun es0 heq ↦ replConst_step_conjElimRight U.R hA (ih es0 heq)
  | impIntro p d ih => exact fun es0 heq ↦ replConst_step_impIntro U.R p (ih es0 heq)
  | impElim hA hB dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_impElim U.R hA hB (ihA es0 heq) (ihB es0 heq)
  | allIntro d ih => exact fun es0 heq ↦ replConst_step_allIntro U.R (ih es0 heq)
  | allElim t hA d ih => exact fun es0 heq ↦ replConst_step_allElim U.R t hA (ih es0 heq)
  | exIntro t hA d ih => exact fun es0 heq ↦ replConst_step_exIntro U.R t hA (ih es0 heq)
  | exElim hA dA dB ihA ihB =>
      exact fun es0 heq ↦ replConst_step_exElim U.R hA (ihA es0 heq) (ihB es0 heq)
  | classical hA d ih => exact fun es0 heq ↦ replConst_step_classical U.R hA (ih es0 heq)
  | chooseHyp p w hA d ih => exact fun es0 heq ↦ replConst_step_chooseHyp U.R p w hA (ih es0 heq)

/-- **Erasing a declaration below a type definition.** -/
theorem HistoryDerivation.erase_below (G : TypeDefGate S) (U : Unfolder S)
    (hB : U.Below G) {es0 : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (ModelExtension.typeDefinition G :: U.step :: es0) s) :
    HistoryDerivation S (ModelExtension.typeDefinition (G.unfold U hB) :: es0)
      (s.replConst U.R) :=
  HistoryDerivation.erase_below_aux G U hB d es0 rfl

end QEDFV.HOL
