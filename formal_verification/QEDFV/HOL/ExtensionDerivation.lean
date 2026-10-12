import QEDFV.HOL.Conservativity

namespace QEDFV.HOL

/-! Derivations are indexed by the declaration history in which they are used.
The head of a history is its newest extension. -/
inductive ExtensionDerivation (S : Signature) :
    List (Extension S) → {Γ : List Ty} → Sequent S Γ → Prop where
  | core {es Γ} {s : Sequent S Γ} (d : Derivation S s) :
      ExtensionDerivation S es s
  | weaken {es Γ} {s : Sequent S Γ} (e : Extension S)
      (d : ExtensionDerivation S es s) (hOld : e.oldLanguage s) :
      ExtensionDerivation S (e :: es) s
  | definition {es} (D : DefinitionGate S)
      (hFresh : D.id ∉ extensionHistoryIds es) :
      ExtensionDerivation S (.definition D :: es)
        { hyps := [], concl := D.head.equal D.rhs }
  | specification {es} (E : SpecificationExtension S)
      (hFresh : E.gate.id ∉ extensionHistoryIds es)
      (d : ExtensionDerivation S es { hyps := [], concl := E.gate.body }) :
      ExtensionDerivation S (.specification E :: es)
        { hyps := [], concl := E.gate.predicate.substitute
            (Sub.single (E.gate.constant E.typeEq)) }

theorem extension_derivation_sound (I : ConstVal S)
    {es : List (Extension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) :
    Valid (interpretSequence es I) s := by
  induction d with
  | core d =>
      exact derivation_sound select_natural (interpretSequence _ I) d
  | weaken e d hOld ih =>
      change Valid (e.interpret (interpretSequence _ I)) _
      exact (e.valid_iff (interpretSequence _ I) _ hOld).2 ih
  | definition D hFresh =>
      exact valid_definition_equation D (interpretSequence _ I)
  | specification E hFresh d ih =>
      exact E.valid_gate (interpretSequence _ I) ih

theorem typed_extension_derivation_sound
    {es : List (Extension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S es s) :
    Valid (interpretSequence es (canonicalConstVal S)) s :=
  extension_derivation_sound (canonicalConstVal S) d

end QEDFV.HOL
