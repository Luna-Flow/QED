import QEDFV.HOL.ExtensionDerivation
import QEDFV.HOL.Concrete
import QEDFV.HOL.ConnectiveRules

/-! A full inference calculus at a fixed declaration history. Extension products can be
premises of the ordinary core rules, and composed derivations can witness later specification
and type-definition steps. The signature remains total and fixed; this module does not model
growing signatures or the executable kernel's state representation. -/
namespace QEDFV.HOL

/-- History-indexed derivations closed under the core inference rules and declaration gates.
`extension` preserves the previously checked extension calculus as an embedded fragment.
Freshness and old-language premises retain the contracts of `ExtensionDerivation`. -/
inductive HistoryDerivation (S : Signature) :
    List (ModelExtension S) → {Γ : List Ty} → Sequent S Γ → Prop where
  | core {es Γ} {s : Sequent S Γ} (d : Derivation S s) :
      HistoryDerivation S es s
  | extension {es Γ} {s : Sequent S Γ} (d : ExtensionDerivation S es s) :
      HistoryDerivation S es s
  | weaken {es Γ} {s : Sequent S Γ} (e : ModelExtension S)
      (d : HistoryDerivation S es s) (hOld : e.oldLanguage s) :
      HistoryDerivation S (e :: es) s
  | definition {es} (D : DefinitionGate S)
      (hFresh : D.id ∉ modelHistoryIds es) :
      HistoryDerivation S (.definition D :: es)
        { hyps := [], concl := D.head.equal D.rhs }
  | specification {es} (E : SpecificationExtension S)
      (hFresh : E.gate.id ∉ modelHistoryIds es)
      (d : HistoryDerivation S es { hyps := [], concl := E.gate.body }) :
      HistoryDerivation S (.specification E :: es)
        { hyps := [], concl := E.gate.predicate.substitute
            (Sub.single (E.gate.constant E.typeEq)) }
  | typedef {es} (G : TypeDefGate S) (l : TypeDefLaw)
      (hk : G.k ∉ modelHistoryTyCons es) (hrep : G.rep ∉ modelHistoryIds es)
      (habs : G.abs ∉ modelHistoryIds es) (w : Term S [] G.repTy)
      (d : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) :
      HistoryDerivation S (.typeDefinition G :: es) (l.sequent G)
  | addAssum {es Γ} {A : Sequent S Γ} (p : Term S Γ .bool)
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := p :: A.hyps, concl := A.concl }
  /-- Hypotheses are a set: any list containing the hypotheses of a derived sequent may
  replace them. The kernel compares hypotheses logically, so this is a structural rule. -/
  | weakenHyps {es Γ} {A : Sequent S Γ} (L : List (Term S Γ .bool))
      (hL : ∀ h, h ∈ A.hyps → h ∈ L) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := L, concl := A.concl }
  | trans {es Γ} {a : Ty} {A B : Sequent S Γ} {x y z : Term S Γ a}
      (hA : A.concl = x.equal y) (hB : B.concl = y.equal z)
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es { hyps := union A.hyps B.hyps, concl := x.equal z }
  | mkComb {es Γ} {a b : Ty} {A B : Sequent S Γ}
      {f g : Term S Γ (.arr a b)} {x y : Term S Γ a}
      (hA : A.concl = f.equal g) (hB : B.concl = x.equal y)
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es
        { hyps := union A.hyps B.hyps, concl := (f.app x).equal (g.app y) }
  | abs {es Γ} {a b : Ty} {A : Sequent S Γ} {s t : Term S (a :: Γ) b}
      (d : HistoryDerivation S es
        { hyps := (weakenSequent A).hyps, concl := s.equal t }) :
      HistoryDerivation S es
        { hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) }
  | eqMp {es Γ} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = p.equal q) (hB : B.concl = p)
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es { hyps := union A.hyps B.hyps, concl := q }
  | deduct {es Γ} {A B : Sequent S Γ}
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es
        { hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl)
        , concl := A.concl.equal B.concl }
  | instType {es Γ} {A : Sequent S Γ} (θ : TypeSub)
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es (typeSubstSequent θ A)
  | instTerm {es Γ Δ} {A : Sequent S Γ} (σ : Sub S Γ Δ)
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es (termSubstSequent σ A)
  | chooseWitness {es Γ} {a : Ty} (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
      (d : HistoryDerivation S es { hyps := [], concl := p.substitute (Sub.single w) }) :
      HistoryDerivation S es
        { hyps := [], concl := p.substitute
            (Sub.single (Term.choice.app (Term.lam p))) }
  | truthIntro {es Γ} :
      HistoryDerivation S es ({ hyps := [], concl := Term.truth } : Sequent S Γ)
  | falsityElim {es Γ} {A : Sequent S Γ} (q : Term S Γ .bool)
      (hA : A.concl = Term.falsity) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := q }
  | conjIntro {es Γ} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = p) (hB : B.concl = q)
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es { hyps := union A.hyps B.hyps, concl := Term.conj p q }
  | conjElimLeft {es Γ} {A : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := p }
  | conjElimRight {es Γ} {A : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := q }
  | impIntro {es Γ} {A : Sequent S Γ} (p : Term S Γ .bool) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := remove A.hyps p, concl := Term.imp p A.concl }
  | impElim {es Γ} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.imp p q) (hB : B.concl = p)
      (dA : HistoryDerivation S es A) (dB : HistoryDerivation S es B) :
      HistoryDerivation S es { hyps := union A.hyps B.hyps, concl := q }
  | allIntro {es Γ} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (d : HistoryDerivation S es { hyps := (weakenSequent A).hyps, concl := φ }) :
      HistoryDerivation S es { hyps := A.hyps, concl := Term.all φ }
  | allElim {es Γ} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (t : Term S Γ a) (hA : A.concl = Term.all φ) (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := φ.substitute (Sub.single t) }
  | exIntro {es Γ} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (t : Term S Γ a) (hA : A.concl = φ.substitute (Sub.single t))
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := Term.ex φ }
  | exElim {es Γ} {a : Ty} {A B : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (hA : A.concl = Term.ex φ) (dA : HistoryDerivation S es A)
      (dB : HistoryDerivation S es { hyps := φ :: (weakenSequent B).hyps,
                                      concl := weakenTerm B.concl }) :
      HistoryDerivation S es { hyps := union A.hyps B.hyps, concl := B.concl }
  | classical {es Γ} {A : Sequent S Γ} {p : Term S Γ .bool}
      (hA : A.concl = Term.imp (Term.imp p Term.falsity) Term.falsity)
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := p }
  | chooseHyp {es Γ} {a : Ty} {A : Sequent S Γ} (p : Term S (a :: Γ) .bool)
      (w : Term S Γ a) (hA : A.concl = p.substitute (Sub.single w))
      (d : HistoryDerivation S es A) :
      HistoryDerivation S es { hyps := A.hyps, concl := p.substitute (Sub.single (Term.choice.app (Term.lam p))) }

/-- Every full history derivation is valid at the history's model pair. Locality is
preserved by every extension; witness derivations are interpreted at the preceding history. -/
theorem history_derivation_sound (M : Model S) (hM : M.IsLocal)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S es s) : Valid (interpretModels es M).I s := by
  induction d with
  | core d => exact derivation_sound select_natural (interpretModels _ M).I d
  | extension d => exact extension_derivation_sound M hM d
  | weaken e d hOld ih =>
      change Valid (e.interpret (interpretModels _ M)).I _
      exact (e.valid_iff (interpretModels _ M) _ hOld
        fun c _ ↦ interpretModels_isLocal _ hM c).2 ih
  | @definition es D hFresh =>
      exact valid_definition_equation D (interpretModels es M).I
        (fun c ↦ interpretModels_isLocal _ hM c)
  | specification E hFresh d ih => exact E.valid_gate (interpretModels _ M).I (fun c ↦ interpretModels_isLocal _ hM c) ih
  | typedef G l hk hrep habs w d ih =>
      exact G.valid_law (interpretModels _ M)
        (fun c _ ↦ interpretModels_isLocal _ hM c) (G.witnessAt_of_valid _ w ih) l
  | addAssum p d ih => exact valid_add_assum (interpretModels _ M).I _ p ih
  | weakenHyps L hL d ih =>
      intro ρ hρ η hh
      exact ih ρ hρ η fun h hmem ↦ hh h (hL h hmem)
  | trans hA hB dA dB ihA ihB =>
      exact valid_trans (interpretModels _ M).I _ _ _ _ _ hA hB ihA ihB
  | mkComb hA hB dA dB ihA ihB =>
      exact valid_mkComb (interpretModels _ M).I _ _ _ _ _ _ hA hB ihA ihB
  | abs d ih => exact valid_abs (interpretModels _ M).I _ _ _ ih
  | eqMp hA hB dA dB ihA ihB =>
      exact valid_eqMp (interpretModels _ M).I _ _ _ _ hA hB ihA ihB
  | deduct dA dB ihA ihB => exact valid_deduct (interpretModels _ M).I _ _ ihA ihB
  | instType θ d ih => exact valid_inst_type select_natural (interpretModels _ M).I θ _ ih
  | instTerm σ d ih => exact valid_inst_term (interpretModels _ M).I σ _ ih
  | chooseWitness p w d ih => exact valid_choose_from_witness (interpretModels _ M).I p w ih
  | truthIntro => exact valid_truth _
  | falsityElim q hA d ih => exact valid_falsity_elim _ _ q hA ih
  | conjIntro hA hB dA dB ihA ihB => exact valid_conj_intro _ _ _ _ _ hA hB ihA ihB
  | conjElimLeft hA d ih => exact valid_conj_elim_left _ _ _ _ hA ih
  | conjElimRight hA d ih => exact valid_conj_elim_right _ _ _ _ hA ih
  | impIntro p d ih => exact valid_imp_intro _ _ p ih
  | impElim hA hB dA dB ihA ihB => exact valid_imp_elim _ _ _ _ _ hA hB ihA ihB
  | allIntro d ih => exact valid_all_intro _ _ _ ih
  | allElim t hA d ih => exact valid_all_elim _ _ _ t hA ih
  | exIntro t hA d ih => exact valid_ex_intro _ _ _ t hA ih
  | exElim hA dA dB ihA ihB => exact valid_ex_elim _ _ _ _ hA ihA ihB
  | classical hA d ih => exact valid_classical _ _ _ hA ih
  | chooseHyp p w hA d ih => exact valid_choose_hyp _ _ p w hA ih

/-- Canonical admissible models discharge the locality premise of history soundness. -/
theorem typed_history_derivation_sound {κ : TyConVal} (hκ : κ.IsAdmissible)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S es s) :
    Valid (interpretModels es (Model.canonical hκ S)).I s :=
  history_derivation_sound (Model.canonical hκ S) (Model.canonical_isLocal hκ S) d

/-- The full calculus preserves the existing semantic old-language conservativity result. -/
theorem history_derivation_old_language_valid {κ : TyConVal} (hκ : κ.IsAdmissible)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S es s) (hOld : oldLanguageModels es s) :
    Valid (canonicalConstVal κ S) s :=
  (typed_global_semantic_conservativity_models hκ es s hOld).1
    (typed_history_derivation_sound hκ d)

/-- The generic false sentence is underivable in the full history calculus. This uses an
admissible local model, so history soundness is applied non-vacuously. -/
theorem history_generic_false_not_derivable (S : Signature)
    (es : List (ModelExtension S)) :
    ¬ HistoryDerivation S es { hyps := [], concl := signatureGenericFalseSentence S } := by
  intro d
  exact signatureGenericFalseSentence_not_valid S (interpretModels es (Model.default S)).I
    ⟨fun _ ↦ ⟨()⟩, (interpretModels es (Model.default S)).adm⟩
    (typed_history_derivation_sound defaultTyCon_isAdmissible d)

end QEDFV.HOL
