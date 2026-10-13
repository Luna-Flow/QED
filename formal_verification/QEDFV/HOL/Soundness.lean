import QEDFV.HOL.Conservativity
import QEDFV.HOL.ExtensionDerivation
import QEDFV.HOL.HistoryDerivation
import QEDFV.HOL.HistoryDerivationExamples
import QEDFV.HOL.HistoryAuditExamples
import QEDFV.HOL.DeclarationAllocation
import QEDFV.HOL.DeclarationAllocationExamples
import QEDFV.HOL.Specification
import QEDFV.HOL.TypeDefinitions
import QEDFV.HOL.Concrete
import QEDFV.HOL.TyConCongruence
import QEDFV.HOL.ModelExtension
import QEDFV.HOL.TypeDefExamples
import QEDFV.HOL.TypeDefDerivationExamples

namespace QEDFV.HOL

variable {κ : TyConVal}

/-! Public Typed HOL soundness entry points. These declarations only compose the
independent proofs in the intrinsically typed HOL namespace; any MoonBit
refinement remains outside this semantic package. -/

structure TypedHOLModel (κ : TyConVal) (S : Signature) where
  constVal : ConstVal κ S
  choiceNatural : ChoiceNatural

noncomputable def canonicalModel (κ : TyConVal) (S : Signature) : TypedHOLModel κ S :=
  { constVal := canonicalConstVal κ S
  , choiceNatural := select_natural }

noncomputable def canonicalExtendedModel
    (es : List (Extension κ S)) : TypedHOLModel κ S :=
  { constVal := interpretSequence es (canonicalConstVal κ S)
  , choiceNatural := select_natural }

theorem typed_model_nonempty (κ : TyConVal) (S : Signature) : Nonempty (TypedHOLModel κ S) :=
  ⟨canonicalModel κ S⟩

theorem typed_extended_model_nonempty
    (es : List (Extension κ S)) : Nonempty (TypedHOLModel κ S) :=
  ⟨canonicalExtendedModel es⟩

theorem typed_canonical_derivation_sound
    {S : Signature} {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) : Valid (canonicalConstVal κ S) s :=
  derivation_sound select_natural (canonicalConstVal κ S) d

theorem TypedHOLModel.derivation_sound
    (M : TypedHOLModel κ S) {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) : Valid M.constVal s :=
  QEDFV.HOL.derivation_sound M.choiceNatural M.constVal d

theorem typed_derivation_sound_all
    {S : Signature} {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    ∀ (M : TypedHOLModel κ S), Valid M.constVal s := by
  intro M
  exact M.derivation_sound d

theorem typed_choice_natural : ChoiceNatural :=
  select_natural

theorem typed_finite_extension_semantic_conservativity
    (es : List (Extension κ S)) {Γ : List Ty} (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s) :
    Valid (interpretSequence es (canonicalConstVal κ S)) s ↔
      Valid (canonicalConstVal κ S) s :=
  typed_global_semantic_conservativity es s hOld

theorem typed_extended_derivation_sound
    (es : List (Extension κ S)) {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    Valid (interpretSequence es (canonicalConstVal κ S)) s :=
  typed_derivation_sound_in_extension es d

theorem typed_definition_semantic_conservativity
    (D : DefinitionGate S) (I : ConstVal κ S) (s : Sequent S Γ)
    (hOld : D.id ∉ s.constIds) :
    Valid (I.withDefinition D) s ↔ Valid I s :=
  valid_definition_old_language_iff D I s hOld

theorem typed_specification_semantic_conservativity
    (G : SpecificationGate S) (I : ConstVal κ S) (hTy : S G.id = G.ty)
    (s : Sequent S Γ) (hOld : G.id ∉ s.constIds) :
    Valid (I.withSpecification G hTy) s ↔ Valid I s :=
  G.valid_old_language_iff I hTy s hOld

theorem typed_type_definition_nonempty
    (C : TypeDefContract κ) (ρ : TypeVal) (hρ : Admissible κ ρ) :
    Nonempty {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.nonempty ρ hρ

theorem typed_concrete_consistency
    :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence } :=
  falseSentence_not_derivable select_natural

theorem typed_signature_generic_consistency (S : Signature) :
    ¬ Derivation S { hyps := [], concl := signatureGenericFalseSentence S } :=
  signatureGenericFalseSentence_not_derivable S select_natural

theorem typed_signature_generic_nonvalid_in_extension
    (es : List (Extension κ S)) (hκ : Admissible κ baseTypeVal) :
    ¬ Valid (interpretSequence es (canonicalConstVal κ S))
      { hyps := [], concl := signatureGenericFalseSentence S } :=
  signatureGenericFalseSentence_not_valid S
    (interpretSequence es (canonicalConstVal κ S)) hκ

/-! The complete mathematical deliverable for the Typed HOL mainline.  Every
field is a theorem or a constructed witness; there is no model-law, gate, or
implementation-correctness assumption hidden in this package. -/
structure TypedHOLCoreProofPackage : Prop where
  choiceNatural : ChoiceNatural
  carrierNonempty :
    ∀ {κ : TyConVal} (a : Ty) (ρ : TypeVal), Admissible κ ρ → Nonempty (a.denote κ ρ)
  modelNonempty :
    ∀ (κ : TyConVal) (S : Signature), Nonempty (TypedHOLModel κ S)
  renameEvaluation :
    ∀ {κ : TyConVal} {S : Signature} {Γ Δ : List Ty} {a : Ty} (I : ConstVal κ S)
      (ρ : TypeVal) (hρ : Admissible κ ρ) (t : Term S Γ a) (r : Ren Γ Δ)
      (η : Env κ ρ Δ),
      (t.rename r).eval I ρ hρ η = t.eval I ρ hρ (Env.pull η r)
  substitutionEvaluation :
    ∀ {κ : TyConVal} {S : Signature} {Γ Δ : List Ty} {a : Ty} (I : ConstVal κ S)
      (ρ : TypeVal) (hρ : Admissible κ ρ) (t : Term S Γ a)
      (σ : Sub S Γ Δ) (η : Env κ ρ Δ),
      (t.substitute σ).eval I ρ hρ η =
        t.eval I ρ hρ (Sub.evalSubst σ I ρ hρ η)
  betaEvaluation :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} {a b : Ty} (I : ConstVal κ S)
      (ρ : TypeVal) (hρ : Admissible κ ρ) (η : Env κ ρ Γ)
      (t : Term S (a :: Γ) b) (x : Term S Γ a),
      (Term.app (.lam t) x).eval I ρ hρ η =
        (t.substitute (Sub.single x)).eval I ρ hρ η
  typeInstantiationEvaluation :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} {a : Ty} (I : ConstVal κ S)
      (ρ : TypeVal) (hρ : Admissible κ ρ) (t : Term S Γ a) (θ : TypeSub)
      (η : Env κ ρ (Γ.map (Ty.subst θ))),
      HEq ((t.instType θ).eval I ρ hρ η)
        (t.eval I (θ.pull κ ρ) (θ.pull_admissible κ ρ hρ) (Env.instPull θ η))
  derivationSound :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} {s : Sequent S Γ},
      Derivation S s → ∀ (I : ConstVal κ S), Valid I s
  addAssumSound :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} (I : ConstVal κ S)
      (s : Sequent S Γ) (p : Term S Γ .bool),
      Valid I s → Valid I { hyps := p :: s.hyps, concl := s.concl }
  choiceSpecificationSound :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} {a : Ty} (I : ConstVal κ S)
      (p : Term S (a :: Γ) .bool) (w : Term S Γ a),
      Valid I { hyps := [], concl := p.substitute (Sub.single w) } →
      Valid I { hyps := [], concl := p.substitute (Sub.single (Term.choice.app (Term.lam p))) }
  definitionEquation :
    ∀ {κ : TyConVal} {S : Signature} (D : DefinitionGate S) (I : ConstVal κ S),
      Valid (I.withDefinition D)
        { hyps := [], concl := (D.head.equal D.rhs) }
  definitionConservativity :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} (D : DefinitionGate S) (I : ConstVal κ S)
      (s : Sequent S Γ), D.id ∉ s.constIds →
      (Valid (I.withDefinition D) s ↔ Valid I s)
  specificationValidity :
    ∀ {κ : TyConVal} {S : Signature} (G : SpecificationGate S) (I : ConstVal κ S)
      (hTy : S G.id = G.ty)
      (d : Derivation S { hyps := [], concl := G.body }),
      let _witnessDerivation := d
      Valid (I.withSpecification G hTy)
        { hyps := [], concl := G.predicate.substitute
            (Sub.single (G.constant hTy)) }
  specificationConservativity :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} (G : SpecificationGate S) (I : ConstVal κ S)
      (hTy : S G.id = G.ty) (s : Sequent S Γ), G.id ∉ s.constIds →
      (Valid (I.withSpecification G hTy) s ↔ Valid I s)
  extensionDerivationSound :
    ∀ {S : Signature} (M : Model S), M.IsLocal →
      ∀ {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ},
        ExtensionDerivation S es s → Valid (interpretModels es M).I s
  extensionDerivationConservative :
    ∀ {κ : TyConVal} {S : Signature}, κ.IsAdmissible → ∀ {es : List (ModelExtension S)}
      {Γ : List Ty} {s : Sequent S Γ},
      ExtensionDerivation S es s → oldLanguageModels es s → Valid (canonicalConstVal κ S) s
  stepPreservesLocality :
    ∀ {S : Signature} (e : ModelExtension S) {M : Model S}, M.IsLocal → (e.interpret M).IsLocal
  typeDefinitionNonempty :
    ∀ {κ : TyConVal} (C : TypeDefContract κ) (ρ : TypeVal) (hρ : Admissible κ ρ),
      Nonempty {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}
  typeDefinitionAbsRep :
    ∀ {κ : TyConVal} (C : TypeDefContract κ) (ρ : TypeVal) (hρ : Admissible κ ρ)
      (x : {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}),
      C.abs ρ hρ (C.rep ρ hρ x) = x
  typeDefinitionRepRange :
    ∀ {κ : TyConVal} (C : TypeDefContract κ) (ρ : TypeVal) (hρ : Admissible κ ρ)
      (x : {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}),
      C.family.pred ρ hρ (C.rep ρ hρ x)
  typeDefinitionRepAbs :
    ∀ {κ : TyConVal} (C : TypeDefContract κ) (ρ : TypeVal) (hρ : Admissible κ ρ)
      {x : Ty.denote κ ρ C.family.repTy}, C.family.pred ρ hρ x →
      C.rep ρ hρ (C.abs ρ hρ x) = x
  typeDefinitionGateAdmissible :
    ∀ {S : Signature} (G : TypeDefGate S) (M : Model S), (G.interpret M).κ.IsAdmissible
  typeDefinitionGateLaws :
    ∀ {S : Signature} (G : TypeDefGate S) (M : Model S), G.PredLocal M.I → G.WitnessAt M.I →
      Valid (G.interpret M).I G.absRepSequent ∧ Valid (G.interpret M).I G.repRangeSequent ∧
        Valid (G.interpret M).I G.repAbsSequent
  typeDefinitionGateConservativity :
    ∀ {S : Signature} {Γ : List Ty} (G : TypeDefGate S) (M : Model S) (s : Sequent S Γ),
      (ModelExtension.typeDefinition G).oldLanguage s → (∀ c, c ∈ s.constIds → M.I.Local c) →
      (Valid (G.interpret M).I s ↔ Valid M.I s)
  finiteExtensionConservativity :
    ∀ {κ : TyConVal} {S : Signature} {Γ : List Ty} (es : List (Extension κ S))
      (s : Sequent S Γ), oldLanguageSequence es s →
      (Valid (interpretSequence es (canonicalConstVal κ S)) s ↔
        Valid (canonicalConstVal κ S) s)
  historyConservativity :
    ∀ {S : Signature} {Γ : List Ty} (es : List (ModelExtension S)) (M : Model S),
      M.IsLocal → ∀ (s : Sequent S Γ), oldLanguageModels es s →
        (Valid (interpretModels es M).I s ↔ Valid M.I s)
  concreteConsistency :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence }
  infinityAnchor :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ
  infinitySentenceValidity :
    ∀ {κ : TyConVal} (S : Signature) (I : ConstVal κ S),
      Valid I { hyps := [], concl := indInfinitySentence S }
  signatureGenericConsistency :
    ∀ (S : Signature),
      ¬ Derivation S { hyps := [], concl := signatureGenericFalseSentence S }
  signatureGenericExtensionNonvalidity :
    ∀ {κ : TyConVal} {S : Signature} (es : List (Extension κ S)),
      Admissible κ baseTypeVal →
      ¬ Valid (interpretSequence es (canonicalConstVal κ S))
        { hyps := [], concl := signatureGenericFalseSentence S }
  signatureGenericHistoryNonvalidity :
    ∀ {S : Signature} (es : List (ModelExtension S)) (M : Model S),
      ¬ Valid (interpretModels es M).I { hyps := [], concl := signatureGenericFalseSentence S }

noncomputable def typedHOLCoreProofPackage : TypedHOLCoreProofPackage := by
  refine {
    choiceNatural := select_natural
    carrierNonempty := ?_
    modelNonempty := ?_
    renameEvaluation := ?_
    substitutionEvaluation := ?_
    betaEvaluation := ?_
    typeInstantiationEvaluation := ?_
    derivationSound := ?_
    addAssumSound := ?_
    choiceSpecificationSound := ?_
    definitionEquation := ?_
    definitionConservativity := ?_
    specificationValidity := ?_
    specificationConservativity := ?_
    extensionDerivationSound := ?_
    extensionDerivationConservative := ?_
    stepPreservesLocality := ?_
    typeDefinitionNonempty := ?_
    typeDefinitionAbsRep := ?_
    typeDefinitionRepRange := ?_
    typeDefinitionRepAbs := ?_
    typeDefinitionGateAdmissible := ?_
    typeDefinitionGateLaws := ?_
    typeDefinitionGateConservativity := ?_
    finiteExtensionConservativity := ?_
    historyConservativity := ?_
    concreteConsistency := typed_concrete_consistency
    infinityAnchor := standard_ind_infinity_anchor
    infinitySentenceValidity := indInfinitySentence_valid
    signatureGenericConsistency := typed_signature_generic_consistency
    signatureGenericExtensionNonvalidity := typed_signature_generic_nonvalid_in_extension
    signatureGenericHistoryNonvalidity := typed_signature_generic_nonvalid_in_history
  }
  · exact fun {κ} a ρ hρ ↦ a.carrier_nonempty κ ρ hρ
  · exact typed_model_nonempty
  · intro κ S Γ Δ a I ρ hρ t r η
    exact Term.eval_rename I ρ hρ t r η
  · intro κ S Γ Δ a I ρ hρ t σ η
    exact Term.eval_substitute I ρ hρ t σ η
  · intro κ S Γ a b I ρ hρ η t x
    exact Term.eval_beta I ρ hρ η t x
  · intro κ S Γ a I ρ hρ t θ η
    exact Term.eval_instType select_natural I ρ hρ t θ η
  · intro κ S Γ s d I
    exact derivation_sound select_natural I d
  · intro κ S Γ I s p hValid
    exact valid_add_assum I s p hValid
  · intro κ S Γ a I p w hValid
    exact valid_choose_from_witness I p w hValid
  · intro κ S D I
    exact valid_definition_equation D I
  · intro κ S Γ D I s hOld
    exact valid_definition_old_language_iff D I s hOld
  · intro κ S G I hTy d
    exact G.valid_constant_from_typed_derivation I hTy d
  · intro κ S Γ G I hTy s hOld
    exact G.valid_old_language_iff I hTy s hOld
  · intro S M hM es Γ s d
    exact extension_derivation_sound M hM d
  · intro κ S hκ es Γ s d hOld
    exact extension_derivation_old_language_valid hκ d hOld
  · intro S e M hM
    exact e.interpret_isLocal hM
  · intro κ C ρ hρ
    exact C.nonempty ρ hρ
  · intro κ C ρ hρ x
    exact C.abs_rep ρ hρ x
  · intro κ C ρ hρ x
    exact C.rep_in_range ρ hρ x
  · intro κ C ρ hρ x hx
    exact C.rep_abs_of_pred ρ hρ hx
  · intro S G M
    exact (G.interpret M).adm
  · intro S G M hloc hW
    exact G.laws M hloc hW
  · intro S Γ G M s hOld hloc
    exact (ModelExtension.typeDefinition G).valid_iff M s hOld hloc
  · intro κ S Γ es s hOld
    exact typed_global_semantic_conservativity es s hOld
  · intro S Γ es M hM s hOld
    exact valid_interpretModels_iff es M hM s hOld

theorem typed_hol_core_proof_complete : Nonempty TypedHOLCoreProofPackage :=
  ⟨typedHOLCoreProofPackage⟩

end QEDFV.HOL
