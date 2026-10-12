import QEDFV.HOL.TypeDefGate

/-! Locality of the interpretation after a type-definition step.

`ConstVal.Local` (the value of a constant depends only on the type variables of its schema)
is what old-language transport across a type-definition step needs
(`TypeDefGate.valid_iff_old`). A history of declaration steps can therefore only be traversed
by the soundness induction if every step preserves locality. Definition and specification
steps do (`DefinitionGate.withDefinition_local`, `SpecificationGate.withSpecification_local`,
using the `annotVars` closure fields); this file proves it for a type-definition step: the new
`Rep`/`Abs` depend on the type parameters `0..n-1` only, and every other constant is either
the old (cast) value or a canonical choice. -/
namespace QEDFV.HOL

variable {κ : TyConVal}

theorem heq_choice {A B : Type} (hA : Nonempty A) (hB : Nonempty B) (h : A = B) :
    HEq (Classical.choice hA) (Classical.choice hB) := by
  subst h
  rfl

section Layer

variable {T T' E0 E0' E1 E1' : Type} {P0 : E0 → Prop} {P0' : E0' → Prop}

theorem layerRep_congr (hT : T = SubCarrier E0 P0) (hT' : T' = SubCarrier E0' P0')
    (e : E0 = E1) (e' : E0' = E1') {d : E1} {d' : E1'} (hTT : T = T') (h0 : E0 = E0')
    (h1 : E1 = E1') (hP : HEq P0 P0') (hd : HEq d d') :
    HEq (layerRep hT e d) (layerRep hT' e' d') := by
  subst hTT h0 h1
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hd
  rfl

theorem layerAbs_congr (hT : T = SubCarrier E0 P0) (hT' : T' = SubCarrier E0' P0')
    (e : E0 = E1) (e' : E0' = E1') (hTT : T = T') (h0 : E0 = E0')
    (h1 : E1 = E1') (hP : HEq P0 P0') :
    HEq (layerAbs hT e) (layerAbs hT' e') := by
  subst hTT h0 h1
  obtain rfl := eq_of_heq hP
  rfl

end Layer

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

theorem newTy_typeVars_lt : ∀ i, i ∈ G.newTy.typeVars → i < G.n := by
  intro i hi
  obtain ⟨j, hj⟩ := hi
  have : i = j.val := by simpa [Ty.typeVars] using hj
  exact this ▸ j.isLt

theorem lt_mem_rep_typeVars {i : Nat} (h : i < G.n) : i ∈ (S G.rep).typeVars := by
  rw [G.rep_ty]
  exact Or.inl ⟨⟨i, h⟩, by simp [Ty.typeVars]⟩

theorem lt_mem_abs_typeVars {i : Nat} (h : i < G.n) : i ∈ (S G.abs).typeVars := by
  rw [G.abs_ty]
  exact Or.inr ⟨⟨i, h⟩, by simp [Ty.typeVars]⟩

theorem rho0_congr {ρ ρ' : TypeVal} (h : ∀ i, i < G.n → ρ i = ρ' i) : G.rho0 ρ = G.rho0 ρ' := by
  funext i
  by_cases hi : i < G.n
  · rw [G.rho0_of_lt ρ hi, G.rho0_of_lt ρ' hi]
    exact h i hi
  · simp [rho0, paramVal, hi]

/-- `Rep` depends on the valuation only through the type parameters. -/
theorem repVal_heq (I : ConstVal κ S) {ρ ρ' : TypeVal} (hρ : Admissible (G.newTyCon I) ρ)
    (hρ' : Admissible (G.newTyCon I) ρ') (h : ∀ i, i < G.n → ρ i = ρ' i) :
    HEq (G.repVal I ρ hρ) (G.repVal I ρ' hρ') := by
  have hr := G.rho0_congr h
  unfold repVal
  refine layerRep_congr _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · exact G.newTy.denote_congr_vars _ fun i hi ↦ h i (G.newTy_typeVars_lt i hi)
  · rw [hr]
  · exact G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi)
  · rw [hr]
  · exact heq_choice _ _
      (G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi))

/-- `Abs` depends on the valuation only through the type parameters. -/
theorem absVal_heq (I : ConstVal κ S) {ρ ρ' : TypeVal}
    (h : ∀ i, i < G.n → ρ i = ρ' i) : HEq (G.absVal I ρ) (G.absVal I ρ') := by
  have hr := G.rho0_congr h
  unfold absVal
  refine layerAbs_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact G.newTy.denote_congr_vars _ fun i hi ↦ h i (G.newTy_typeVars_lt i hi)
  · rw [hr]
  · exact G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi)
  · rw [hr]

/-- **The model after a type-definition step is local, if the old one is.** -/
theorem newConst_local (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hI : ∀ c, I.Local c)
    (c : Nat) : (G.newConst hκ I).Local c := by
  intro ρ hρ ρ' hρ' hag
  by_cases ha : c = G.abs
  · subst ha
    rw [G.newConst_abs hκ I ρ hρ, G.newConst_abs hκ I ρ' hρ']
    exact (cast_heq _ _).trans ((G.absVal_heq I fun i hi ↦ hag i (G.lt_mem_abs_typeVars hi)).trans
      (cast_heq _ _).symm)
  by_cases hr : c = G.rep
  · subst hr
    rw [G.newConst_rep hκ I ρ hρ, G.newConst_rep hκ I ρ' hρ']
    exact (cast_heq _ _).trans
      ((G.repVal_heq I hρ hρ' fun i hi ↦ hag i (G.lt_mem_rep_typeVars hi)).trans
        (cast_heq _ _).symm)
  by_cases hk : G.k ∉ (S c).tyCons
  · rw [G.newConst_old hκ I hr ha hk ρ hρ, G.newConst_old hκ I hr ha hk ρ' hρ']
    exact (cast_heq _ _).trans
      ((hI c _ ((G.admissible_new_iff hκ I ρ).mpr hρ) _ ((G.admissible_new_iff hκ I ρ').mpr hρ')
        hag).trans (cast_heq _ _).symm)
  · have e : ∀ (ρ : TypeVal) (hρ : Admissible (G.newTyCon I) ρ),
        G.newConst hκ I ρ hρ c = Classical.choice ((S c).carrier_nonempty _ ρ hρ) := by
      intro ρ hρ
      unfold newConst
      rw [ConstVal.override_agree _ G.abs c _ ha, ConstVal.override_agree _ G.rep c _ hr]
      unfold baseConst
      rw [dif_neg hk]
    rw [e ρ hρ, e ρ' hρ']
    exact heq_choice _ _ ((S c).denote_congr_vars _ hag)

end TypeDefGate

end QEDFV.HOL
