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

noncomputable def canonicalModel (S : Signature) : TypedHOLModel S :=
  { constVal := canonicalConstVal S
  , choiceNatural := select_natural }

theorem typed_model_nonempty (S : Signature) : Nonempty (TypedHOLModel S) :=
  ⟨canonicalModel S⟩

theorem typed_canonical_derivation_sound
    {S : Signature} {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) : Valid (canonicalConstVal S) s :=
  derivation_sound select_natural (canonicalConstVal S) d

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

theorem typed_choice_natural : ChoiceNatural :=
  select_natural

theorem typed_finite_extension_semantic_conservativity
    (es : List (Extension S)) {Γ : List Ty} (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s) :
    Valid (interpretSequence es (canonicalConstVal S)) s ↔
      Valid (canonicalConstVal S) s :=
  typed_global_semantic_conservativity es s hOld

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
    :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence } :=
  falseSentence_not_derivable select_natural

end QEDFV.HOL
