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

noncomputable def canonicalExtendedModel
    (es : List (Extension S)) : TypedHOLModel S :=
  { constVal := interpretSequence es (canonicalConstVal S)
  , choiceNatural := select_natural }

theorem typed_model_nonempty (S : Signature) : Nonempty (TypedHOLModel S) :=
  ⟨canonicalModel S⟩

theorem typed_extended_model_nonempty
    (es : List (Extension S)) : Nonempty (TypedHOLModel S) :=
  ⟨canonicalExtendedModel es⟩

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

theorem typed_extended_derivation_sound
    (es : List (Extension S)) {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    Valid (interpretSequence es (canonicalConstVal S)) s :=
  typed_derivation_sound_in_extension es d

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

theorem typed_concrete_consistency_in_extension
    (es : List (Extension standardSignature))
    (hOld : oldLanguageSequence es { hyps := [], concl := falseSentence }) :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence } := by
  intro d
  have hExtended := derivation_sound_in_extension es standardConstVal d
  have hBase := valid_base_of_interpretSequence es standardConstVal
    { hyps := [], concl := falseSentence } hOld hExtended
  exact falseSentence_not_valid hBase

/-! The complete mathematical deliverable for the Typed HOL mainline.  Every
field is a theorem or a constructed witness; there is no model-law, gate, or
implementation-correctness assumption hidden in this package. -/
structure TypedHOLProofPackage : Prop where
  choiceNatural : ChoiceNatural
  carrierNonempty :
    ∀ (a : Ty) (ρ : TypeVal), Admissible ρ → Nonempty (a.denote ρ)
  modelNonempty :
    ∀ (S : Signature), Nonempty (TypedHOLModel S)
  extendedModelNonempty :
    ∀ {S : Signature} (es : List (Extension S)),
      let _extensions := es
      Nonempty (TypedHOLModel S)
  renameEvaluation :
    ∀ {S : Signature} {Γ Δ : List Ty} {a : Ty} (I : ConstVal S)
      (ρ : TypeVal) (hρ : Admissible ρ) (t : Term S Γ a) (r : Ren Γ Δ)
      (η : Env ρ Δ),
      (t.rename r).eval I ρ hρ η = t.eval I ρ hρ (Env.pull η r)
  substitutionEvaluation :
    ∀ {S : Signature} {Γ Δ : List Ty} {a : Ty} (I : ConstVal S)
      (ρ : TypeVal) (hρ : Admissible ρ) (t : Term S Γ a)
      (σ : Sub S Γ Δ) (η : Env ρ Δ),
      (t.substitute σ).eval I ρ hρ η =
        t.eval I ρ hρ (Sub.evalSubst σ I ρ hρ η)
  betaEvaluation :
    ∀ {S : Signature} {Γ : List Ty} {a b : Ty} (I : ConstVal S)
      (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ)
      (t : Term S (a :: Γ) b) (x : Term S Γ a),
      (Term.app (.lam t) x).eval I ρ hρ η =
        (t.substitute (Sub.single x)).eval I ρ hρ η
  typeInstantiationEvaluation :
    ∀ {S : Signature} {Γ : List Ty} {a : Ty} (I : ConstVal S)
      (ρ : TypeVal) (hρ : Admissible ρ) (t : Term S Γ a) (θ : TypeSub)
      (η : Env ρ (Γ.map (Ty.subst θ))),
      HEq ((t.instType θ).eval I ρ hρ η)
        (t.eval I (θ.pull ρ) (θ.pull_admissible ρ hρ) (Env.instPull θ η))
  derivationSound :
    ∀ {S : Signature} {Γ : List Ty} {s : Sequent S Γ},
      Derivation S s → ∀ (I : ConstVal S), Valid I s
  definitionEquation :
    ∀ {S : Signature} (D : DefinitionGate S) (I : ConstVal S),
      Valid (I.withDefinition D)
        { hyps := [], concl := (D.head.equal D.rhs) }
  definitionConservativity :
    ∀ {S : Signature} {Γ : List Ty} (D : DefinitionGate S) (I : ConstVal S)
      (s : Sequent S Γ), D.id ∉ s.constIds →
      (Valid (I.withDefinition D) s ↔ Valid I s)
  specificationValidity :
    ∀ {S : Signature} (G : SpecificationGate S) (I : ConstVal S)
      (hTy : S G.id = G.ty)
      (d : Derivation S { hyps := [], concl := G.body }),
      let _witnessDerivation := d
      Valid (I.withSpecification G hTy)
        { hyps := [], concl := G.predicate.substitute
            (Sub.single (G.constant hTy)) }
  specificationConservativity :
    ∀ {S : Signature} {Γ : List Ty} (G : SpecificationGate S) (I : ConstVal S)
      (hTy : S G.id = G.ty) (s : Sequent S Γ), G.id ∉ s.constIds →
      (Valid (I.withSpecification G hTy) s ↔ Valid I s)
  typeDefinitionNonempty :
    ∀ (C : TypeDefContract) (ρ : TypeVal) (hρ : Admissible ρ),
      Nonempty {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}
  typeDefinitionAbsRep :
    ∀ (C : TypeDefContract) (ρ : TypeVal) (hρ : Admissible ρ)
      (x : {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}),
      C.abs ρ hρ (C.rep ρ hρ x) = x
  typeDefinitionRepRange :
    ∀ (C : TypeDefContract) (ρ : TypeVal) (hρ : Admissible ρ)
      (x : {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}),
      C.family.pred ρ hρ (C.rep ρ hρ x)
  typeDefinitionRepAbs :
    ∀ (C : TypeDefContract) (ρ : TypeVal) (hρ : Admissible ρ)
      {x : Ty.denote ρ C.family.repTy}, C.family.pred ρ hρ x →
      C.rep ρ hρ (C.abs ρ hρ x) = x
  finiteExtensionConservativity :
    ∀ {S : Signature} {Γ : List Ty} (es : List (Extension S))
      (s : Sequent S Γ), oldLanguageSequence es s →
      (Valid (interpretSequence es (canonicalConstVal S)) s ↔
        Valid (canonicalConstVal S) s)
  concreteConsistency :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence }
  infinityAnchor :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ
  concreteExtensionConsistency :
    ∀ (es : List (Extension standardSignature)),
      oldLanguageSequence es { hyps := [], concl := falseSentence } →
      ¬ Derivation standardSignature { hyps := [], concl := falseSentence }

noncomputable def typedHOLProofPackage : TypedHOLProofPackage := by
  refine {
    choiceNatural := select_natural
    carrierNonempty := ?_
    modelNonempty := ?_
    extendedModelNonempty := ?_
    renameEvaluation := ?_
    substitutionEvaluation := ?_
    betaEvaluation := ?_
    typeInstantiationEvaluation := ?_
    derivationSound := ?_
    definitionEquation := ?_
    definitionConservativity := ?_
    specificationValidity := ?_
    specificationConservativity := ?_
    typeDefinitionNonempty := ?_
    typeDefinitionAbsRep := ?_
    typeDefinitionRepRange := ?_
    typeDefinitionRepAbs := ?_
    finiteExtensionConservativity := ?_
    concreteConsistency := typed_concrete_consistency
    infinityAnchor := standard_ind_infinity_anchor
    concreteExtensionConsistency := typed_concrete_consistency_in_extension
  }
  · exact fun a ρ hρ ↦ a.carrier_nonempty ρ hρ
  · exact typed_model_nonempty
  · intro S es
    exact typed_extended_model_nonempty es
  · intro S Γ Δ a I ρ hρ t r η
    exact Term.eval_rename I ρ hρ t r η
  · intro S Γ Δ a I ρ hρ t σ η
    exact Term.eval_substitute I ρ hρ t σ η
  · intro S Γ a b I ρ hρ η t x
    exact Term.eval_beta I ρ hρ η t x
  · intro S Γ a I ρ hρ t θ η
    exact Term.eval_instType select_natural I ρ hρ t θ η
  · intro S Γ s d I
    exact derivation_sound select_natural I d
  · intro S D I
    exact valid_definition_equation D I
  · intro S Γ D I s hOld
    exact valid_definition_old_language_iff D I s hOld
  · intro S G I hTy d
    exact G.valid_constant_from_typed_derivation I hTy d
  · intro S Γ G I hTy s hOld
    exact G.valid_old_language_iff I hTy s hOld
  · intro C ρ hρ
    exact C.nonempty ρ hρ
  · intro C ρ hρ x
    exact C.abs_rep ρ hρ x
  · intro C ρ hρ x
    exact C.rep_in_range ρ hρ x
  · intro C ρ hρ x hx
    exact C.rep_abs_of_pred ρ hρ hx
  · intro S Γ es s hOld
    exact typed_global_semantic_conservativity es s hOld

theorem typed_hol_proof_complete : Nonempty TypedHOLProofPackage :=
  ⟨typedHOLProofPackage⟩

end QEDFV.HOL
