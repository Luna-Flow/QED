import QEDFV.HOL.Specification

namespace QEDFV.HOL

/-! Typed HOL extension semantics. An extension changes only the interpretation of
fresh constants; type-definition contracts preserve the already non-empty carrier
discipline. This is the complete semantic conservativity layer for the typed core. -/

structure SpecificationExtension (S : Signature) where
  gate : SpecificationGate S
  typeEq : S gate.id = gate.ty

theorem SpecificationExtension.valid_gate
    (E : SpecificationExtension S) (I : ConstVal S)
    (hWitness : Valid I { hyps := [], concl := E.gate.body }) :
    Valid (I.withSpecification E.gate E.typeEq)
      { hyps := [], concl := E.gate.predicate.substitute
          (Sub.single (E.gate.constant E.typeEq)) } :=
  E.gate.valid_constant I E.typeEq hWitness

inductive Extension (S : Signature) where
  | definition (gate : DefinitionGate S)
  | specification (extension : SpecificationExtension S)
  | typeDefinition (contract : TypeDefContract)

def Extension.constantIds (e : Extension S) : Finset Nat :=
  match e with
  | .definition D => {D.id}
  | .specification E => {E.gate.id}
  | .typeDefinition _ => ∅

def extensionHistoryIds (es : List (Extension S)) : Finset Nat :=
  es.foldr (fun e ids ↦ e.constantIds ∪ ids) ∅

def Extension.oldLanguage (e : Extension S) (s : Sequent S Γ) : Prop :=
  match e with
  | .definition D => D.id ∉ s.constIds
  | .specification E => E.gate.id ∉ s.constIds
  | .typeDefinition _ => True

noncomputable def Extension.interpret (e : Extension S) (I : ConstVal S) : ConstVal S :=
  match e with
  | .definition D => I.withDefinition D
  | .specification E => I.withSpecification E.gate E.typeEq
  | .typeDefinition _ => I

theorem Extension.valid_iff
    (e : Extension S) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : e.oldLanguage s) :
    Valid (e.interpret I) s ↔ Valid I s := by
  cases e with
  | definition D =>
      exact valid_definition_old_language_iff D I s hOld
  | specification E =>
      exact E.gate.valid_old_language_iff I E.typeEq s hOld
  | typeDefinition C =>
      simp [Extension.interpret]

noncomputable def interpretSequence (es : List (Extension S)) (I : ConstVal S) : ConstVal S :=
  match es with
  | [] => I
  | e :: rest => e.interpret (interpretSequence rest I)

def oldLanguageSequence (es : List (Extension S)) (s : Sequent S Γ) : Prop :=
  ∀ e, e ∈ es → e.oldLanguage s

theorem valid_interpretSequence_iff
    (es : List (Extension S)) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s) :
    Valid (interpretSequence es I) s ↔ Valid I s := by
  induction es generalizing I with
  | nil =>
      simp [interpretSequence]
  | cons e rest ih =>
      have hHead : e.oldLanguage s := hOld e (by simp)
      have hRest : oldLanguageSequence rest s := by
        intro e' he'
        exact hOld e' (by simp [he'])
      change Valid (e.interpret (interpretSequence rest I)) s ↔ Valid I s
      rw [e.valid_iff (interpretSequence rest I) s hHead]
      exact ih (I := I) hRest

theorem valid_interpretSequence_of_old_language
    (es : List (Extension S)) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s) (hValid : Valid I s) :
    Valid (interpretSequence es I) s :=
  (valid_interpretSequence_iff es I s hOld).2 hValid

theorem valid_base_of_interpretSequence
    (es : List (Extension S)) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s)
    (hValid : Valid (interpretSequence es I) s) :
    Valid I s :=
  (valid_interpretSequence_iff es I s hOld).1 hValid

theorem typed_derivation_sound_in_extension
    (es : List (Extension S)) {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    Valid (interpretSequence es (canonicalConstVal S)) s :=
  derivation_sound select_natural (interpretSequence es (canonicalConstVal S)) d

theorem derivation_sound_in_extension
    (es : List (Extension S)) (I : ConstVal S)
    {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    Valid (interpretSequence es I) s :=
  derivation_sound select_natural (interpretSequence es I) d

theorem typed_global_semantic_conservativity
    (es : List (Extension S)) {Γ : List Ty} (s : Sequent S Γ)
    (hOld : oldLanguageSequence es s) :
    Valid (interpretSequence es (canonicalConstVal S)) s ↔
      Valid (canonicalConstVal S) s :=
  valid_interpretSequence_iff es (canonicalConstVal S) s hOld

end QEDFV.HOL
