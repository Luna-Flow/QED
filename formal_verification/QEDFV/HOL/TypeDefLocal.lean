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

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

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
