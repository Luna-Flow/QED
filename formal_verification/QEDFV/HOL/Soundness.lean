import QEDFV.HOL.Conservativity
import QEDFV.HOL.Specification
import QEDFV.HOL.TypeDefinitions
import QEDFV.HOL.Concrete

namespace QEDFV.HOL

/-! Public Typed HOL soundness entry points. These declarations only compose the
independent proofs in the HOL namespace; the legacy `Lean.Expr` and MoonBit
refinement remains outside this semantic package. -/

structure TypedHOLModel (S : Signature) where
  constVal : ConstVal S
  choiceNatural : ChoiceNatural

theorem TypedHOLModel.derivation_sound
    (M : TypedHOLModel S) {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) : Valid M.constVal s :=
  QEDFV.HOL.derivation_sound M.choiceNatural M.constVal d

theorem typed_derivation_sound_all
    {S : Signature} {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    ∀ (M : TypedHOLModel S), Valid M.constVal s := by
  intro M
  exact M.derivation_sound d

theorem typed_definition_semantic_conservativity
    (D : DefinitionGate S) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : D.id ∉ s.constIds) :
    Valid (I.withDefinition D) s ↔ Valid I s :=
  valid_definition_old_language_iff D I s hOld

theorem typed_specification_semantic_conservativity
    (G : SpecificationGate S) (I : ConstVal S) (hTy : S G.id = G.ty)
    (s : Sequent S Γ) (hOld : G.id ∉ s.constIds) :
    Valid (I.withSpecification G hTy) s ↔ Valid I s :=
  G.valid_old_language_iff I hTy s hOld

theorem typed_type_definition_nonempty
    (C : TypeDefContract) (ρ : TypeVal) (hρ : Admissible ρ) :
    Nonempty {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.nonempty ρ hρ

theorem typed_concrete_consistency
    (hChoice : ChoiceNatural) :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence } :=
  falseSentence_not_derivable hChoice

end QEDFV.HOL
