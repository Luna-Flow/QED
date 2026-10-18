import QEDFV.HOL.Infinity
import QEDFV.HOL.ConnectiveRules

namespace QEDFV.HOL

variable {κ : TyConVal}

/-! A typed HOL derivation object. The sequent index carries the complete
typing information, so malformed rule applications are unrepresentable. -/
inductive Derivation (S : Signature) :
    {Γ : List Ty} → Sequent S Γ → Prop where
  | refl {Γ : List Ty} {a : Ty} (t : Term S Γ a) :
      Derivation S { hyps := [], concl := t.equal t }
  | assume {Γ : List Ty} (p : Term S Γ .bool) :
      Derivation S { hyps := [p], concl := p }
  | addAssum {Γ : List Ty} {A : Sequent S Γ} (p : Term S Γ .bool)
      (d : Derivation S A) :
      Derivation S { hyps := p :: A.hyps, concl := A.concl }
  | trans {Γ : List Ty} {a : Ty} {A B : Sequent S Γ}
      {x y z : Term S Γ a}
      (hA : A.concl = x.equal y) (hB : B.concl = y.equal z)
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S { hyps := union A.hyps B.hyps, concl := x.equal z }
  | mkComb {Γ : List Ty} {a b : Ty} {A B : Sequent S Γ}
      {f g : Term S Γ (.arr a b)} {x y : Term S Γ a}
      (hA : A.concl = f.equal g) (hB : B.concl = x.equal y)
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S
        { hyps := union A.hyps B.hyps, concl := (f.app x).equal (g.app y) }
  | abs {Γ : List Ty} {a b : Ty} {A : Sequent S Γ}
      {s t : Term S (a :: Γ) b}
      (d : Derivation S
        { hyps := (weakenSequent A).hyps, concl := s.equal t }) :
      Derivation S
        { hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) }
  | beta {Γ : List Ty} {a b : Ty} (s : Term S (a :: Γ) b) (x : Term S Γ a) :
      Derivation S
        { hyps := [], concl := (Term.lam s).app x |>.equal (s.substitute (Sub.single x)) }
  | eqMp {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = p.equal q) (hB : B.concl = p)
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S { hyps := union A.hyps B.hyps, concl := q }
  | deduct {Γ : List Ty} {A B : Sequent S Γ}
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S
        { hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl)
        , concl := A.concl.equal B.concl }
  | instType {Γ : List Ty} {A : Sequent S Γ} (θ : TypeSub)
      (d : Derivation S A) :
      Derivation S (typeSubstSequent θ A)
  | instTerm {Γ Δ : List Ty} {A : Sequent S Γ} (σ : Sub S Γ Δ)
      (d : Derivation S A) :
      Derivation S (termSubstSequent σ A)
  | /-- Hilbert choice from an explicitly derived witness. This is an internal
      inference rule, not the `ks_specify_const` declaration extension. -/
    chooseWitness {Γ : List Ty} {a : Ty} (p : Term S (a :: Γ) .bool)
      (w : Term S Γ a)
      (d : Derivation S { hyps := [], concl := p.substitute (Sub.single w) }) :
      Derivation S
        { hyps := [], concl := p.substitute
            (Sub.single (Term.choice.app (Term.lam p))) }
  | indInfinity :
      Derivation S { hyps := [], concl := indInfinitySentence S }
  /-- Rules of the primitive connectives and quantifiers. The kernel defines these as
  constants and derives the same rules; see `ConnectiveRules.lean`. -/
  | truthIntro {Γ : List Ty} :
      Derivation S ({ hyps := [], concl := Term.truth } : Sequent S Γ)
  | falsityElim {Γ : List Ty} {A : Sequent S Γ} (q : Term S Γ .bool)
      (hA : A.concl = Term.falsity) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := q }
  | conjIntro {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = p) (hB : B.concl = q)
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S { hyps := union A.hyps B.hyps, concl := Term.conj p q }
  | conjElimLeft {Γ : List Ty} {A : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.conj p q) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := p }
  | conjElimRight {Γ : List Ty} {A : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.conj p q) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := q }
  | impIntro {Γ : List Ty} {A : Sequent S Γ} (p : Term S Γ .bool) (d : Derivation S A) :
      Derivation S { hyps := remove A.hyps p, concl := Term.imp p A.concl }
  | impElim {Γ : List Ty} {A B : Sequent S Γ} {p q : Term S Γ .bool}
      (hA : A.concl = Term.imp p q) (hB : B.concl = p)
      (dA : Derivation S A) (dB : Derivation S B) :
      Derivation S { hyps := union A.hyps B.hyps, concl := q }
  | allIntro {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (d : Derivation S { hyps := (weakenSequent A).hyps, concl := φ }) :
      Derivation S { hyps := A.hyps, concl := Term.all φ }
  | allElim {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (t : Term S Γ a) (hA : A.concl = Term.all φ) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := φ.substitute (Sub.single t) }
  | exIntro {Γ : List Ty} {a : Ty} {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (t : Term S Γ a) (hA : A.concl = φ.substitute (Sub.single t)) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := Term.ex φ }
  | exElim {Γ : List Ty} {a : Ty} {A B : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
      (hA : A.concl = Term.ex φ) (dA : Derivation S A)
      (dB : Derivation S { hyps := φ :: (weakenSequent B).hyps,
                           concl := weakenTerm B.concl }) :
      Derivation S { hyps := union A.hyps B.hyps, concl := B.concl }
  | classical {Γ : List Ty} {A : Sequent S Γ} {p : Term S Γ .bool}
      (hA : A.concl = Term.imp (Term.imp p Term.falsity) Term.falsity) (d : Derivation S A) :
      Derivation S { hyps := A.hyps, concl := p }

theorem derivation_sound (hChoice : ChoiceNatural) (I : ConstVal κ S)
    {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) : Valid I s := by
  induction d with
  | refl t => exact valid_refl I t
  | assume p => exact valid_assume I p
  | addAssum p d ih => exact valid_add_assum I _ p ih
  | trans hA hB dA dB ihA ihB =>
      exact valid_trans I _ _ _ _ _ hA hB ihA ihB
  | mkComb hA hB dA dB ihA ihB =>
      exact valid_mkComb I _ _ _ _ _ _ hA hB ihA ihB
  | abs d ih =>
      exact valid_abs I _ _ _ ih
  | beta s x => exact valid_beta I s x
  | eqMp hA hB dA dB ihA ihB =>
      exact valid_eqMp I _ _ _ _ hA hB ihA ihB
  | deduct dA dB ihA ihB => exact valid_deduct I _ _ ihA ihB
  | instType θ d ih => exact valid_inst_type hChoice I θ _ ih
  | instTerm σ d ih => exact valid_inst_term I σ _ ih
  | chooseWitness p w d ih => exact valid_choose_from_witness I p w ih
  | indInfinity => exact indInfinitySentence_valid S I
  | truthIntro => exact valid_truth I
  | falsityElim q hA d ih => exact valid_falsity_elim I _ q hA ih
  | conjIntro hA hB dA dB ihA ihB => exact valid_conj_intro I _ _ _ _ hA hB ihA ihB
  | conjElimLeft hA d ih => exact valid_conj_elim_left I _ _ _ hA ih
  | conjElimRight hA d ih => exact valid_conj_elim_right I _ _ _ hA ih
  | impIntro p d ih => exact valid_imp_intro I _ p ih
  | impElim hA hB dA dB ihA ihB => exact valid_imp_elim I _ _ _ _ hA hB ihA ihB
  | allIntro d ih => exact valid_all_intro I _ _ ih
  | allElim t hA d ih => exact valid_all_elim I _ _ t hA ih
  | exIntro t hA d ih => exact valid_ex_intro I _ _ t hA ih
  | exElim hA dA dB ihA ihB => exact valid_ex_elim I _ _ _ hA ihA ihB
  | classical hA d ih => exact valid_classical I _ _ hA ih

theorem derivation_sound_all {Γ : List Ty} {s : Sequent S Γ}
    (d : Derivation S s) :
    ∀ (_hChoice : ChoiceNatural) (I : ConstVal κ S), Valid I s := by
  intro hChoice I
  exact derivation_sound hChoice I d

end QEDFV.HOL
