import QEDFV.HOL.Derivation
import QEDFV.HOL.Congruence

namespace QEDFV.HOL

variable {κ : TyConVal}

/-- Evaluation under two constant interpretations of the same constructor interpretation
that agree on the constants occurring in the term. A corollary of `Term.eval_congr_κ`. -/
theorem Term.eval_agree (t : Term S Γ a) (I J : ConstVal κ S)
    (ρ : TypeVal) (hρ : Admissible κ ρ) (η : Env κ ρ Γ)
    (hAgree : ∀ c, c ∈ t.constIds → ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I ρ hρ c = J ρ hρ c) :
    t.eval I ρ hρ η = t.eval J ρ hρ η :=
  eq_of_heq (Term.eval_congr_κ hρ hρ t (TyConVal.AgreeOn.refl κ _)
    (fun c hc ↦ ConstVal.AgreeAt.of_eq (hAgree c hc)) η η (fun _ _ _ ↦ HEq.rfl))

def Sequent.constIds (s : Sequent S Γ) : Finset Nat :=
  s.hyps.foldr (fun h acc ↦ h.constIds ∪ acc) ∅ ∪ s.concl.constIds

theorem mem_foldr_constIds {hs : List (Term S Γ .bool)} {h : Term S Γ .bool}
    (hh : h ∈ hs) : h.constIds ⊆ hs.foldr (fun t acc ↦ t.constIds ∪ acc) ∅ := by
  induction hs with
  | nil => cases hh
  | cons x xs ih =>
      simp only [List.mem_cons] at hh
      simp only [List.foldr]
      cases hh with
      | inl hhead =>
          subst h
          exact fun c hc ↦ Finset.mem_union_left _ hc
      | inr htail =>
          intro c hc
          exact Finset.mem_union_right _ (ih htail hc)

theorem Sequent.mem_constIds_hyp {s : Sequent S Γ} {h : Term S Γ .bool}
    (hh : h ∈ s.hyps) : h.constIds ⊆ s.constIds := by
  intro c hc
  exact Finset.mem_union_left _ (mem_foldr_constIds hh hc)

theorem Sequent.mem_constIds_concl {s : Sequent S Γ} {c : Nat}
    (hc : c ∈ s.concl.constIds) : c ∈ s.constIds := by
  simp [Sequent.constIds, hc]

/-- Cross-model transport of validity. A sequent valid under `(κ, I)` is valid under
`(κ', J)` when the two models agree on the sequent's language: the constructor
interpretations agree on the constructor ids of the sequent (`Sequent.tyCons`), the constants
occurring agree (`ConstVal.AgreeAt`), and the two interpretations admit the same type
valuations. The admissibility hypothesis is necessary: validity is vacuous under a
constructor interpretation that is not admissible. -/
theorem valid_transport_κ {s : Sequent S Γ} {κ' : TyConVal} (I : ConstVal κ S)
    (J : ConstVal κ' S) (hAdm : ∀ ρ, Admissible κ' ρ → Admissible κ ρ)
    (hC : κ.AgreeOn s.tyCons κ')
    (hAgree : ∀ c, c ∈ s.constIds → I.AgreeAt J s.tyCons c)
    (hValid : Valid I s) : Valid J s := by
  intro ρ hρ' η' hh
  have hρ : Admissible κ ρ := hAdm ρ hρ'
  let η : Env κ ρ Γ := Env.crossCast s.tyCons hC hρ η'
  have hη : ∀ b (v : Var Γ b), b.tyCons ⊆ s.tyCons → HEq (η b v) (η' b v) :=
    fun b v h ↦ Env.crossCast_heq s.tyCons hC hρ η' b v h
  have hcong : ∀ (t : Term S Γ .bool), t.tyCons ⊆ s.tyCons → t.constIds ⊆ s.constIds →
      t.eval I ρ hρ η = t.eval J ρ hρ' η' := fun t ht hk ↦
    eq_of_heq (Term.eval_congr_κ hρ hρ' t (hC.mono ht)
      (fun c hc ↦ (hAgree c (hk hc)).mono ht) η η'
      (fun b v h ↦ hη b v (h.trans ht)))
  have hHyp : ∀ h, h ∈ s.hyps → h.eval I ρ hρ η := by
    intro h hmem
    rw [hcong h (Sequent.tyCons_hyp hmem) (Sequent.mem_constIds_hyp hmem)]
    exact hh h hmem
  have hConcl := hValid ρ hρ η hHyp
  rw [← hcong s.concl (Sequent.tyCons_concl s) (fun c hc ↦ Sequent.mem_constIds_concl hc)]
  exact hConcl

/-- Validity is invariant under a change of model that preserves the sequent's language:
the iff version of `valid_transport_κ`. -/
theorem valid_iff_κ {s : Sequent S Γ} {κ' : TyConVal} (I : ConstVal κ S)
    (J : ConstVal κ' S) (hAdm : ∀ ρ, Admissible κ ρ ↔ Admissible κ' ρ)
    (hC : κ.AgreeOn s.tyCons κ')
    (hAgree : ∀ c, c ∈ s.constIds → I.AgreeAt J s.tyCons c) :
    Valid I s ↔ Valid J s :=
  ⟨valid_transport_κ I J (fun ρ h ↦ (hAdm ρ).mpr h) hC hAgree,
   valid_transport_κ J I (fun ρ h ↦ (hAdm ρ).mp h) hC.symm
     (fun c hc ↦ (hAgree c hc).symm)⟩

theorem valid_transport {s : Sequent S Γ} (I J : ConstVal κ S)
    (hAgree : ∀ c, c ∈ s.constIds → ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I ρ hρ c = J ρ hρ c) (hValid : Valid I s) :
    Valid J s :=
  valid_transport_κ I J (fun _ h ↦ h) (TyConVal.AgreeOn.refl κ _)
    (fun c hc ↦ ConstVal.AgreeAt.of_eq (hAgree c hc)) hValid

def oldLanguage (oldIds : Finset Nat) (s : Sequent S Γ) : Prop :=
  s.constIds ⊆ oldIds

theorem valid_old_language_transport {oldIds : Finset Nat} {s : Sequent S Γ}
    (hOld : oldLanguage oldIds s) (I J : ConstVal κ S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I ρ hρ c = J ρ hρ c) (hValid : Valid I s) :
    Valid J s := by
  apply valid_transport I J
  intro c hc ρ hρ
  exact hAgree c (hOld hc) ρ hρ
  exact hValid

/-- Old-language invariance across a change of model: constructors may be reinterpreted
outside the sequent's constructor ids. -/
theorem valid_old_language_iff_κ {oldIds : Finset Nat} {s : Sequent S Γ} {κ' : TyConVal}
    (hOld : oldLanguage oldIds s) (I : ConstVal κ S) (J : ConstVal κ' S)
    (hAdm : ∀ ρ, Admissible κ ρ ↔ Admissible κ' ρ) (hC : κ.AgreeOn s.tyCons κ')
    (hAgree : ∀ c, c ∈ oldIds → I.AgreeAt J s.tyCons c) :
    Valid I s ↔ Valid J s :=
  valid_iff_κ I J hAdm hC (fun _ hc ↦ hAgree _ (hOld hc))

theorem valid_old_language_iff {oldIds : Finset Nat} {s : Sequent S Γ}
    (hOld : oldLanguage oldIds s) (I J : ConstVal κ S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I ρ hρ c = J ρ hρ c) :
    Valid I s ↔ Valid J s :=
  valid_old_language_iff_κ hOld I J (fun _ ↦ Iff.rfl) (TyConVal.AgreeOn.refl κ _)
    (fun c hc ↦ ConstVal.AgreeAt.of_eq (hAgree c hc))

theorem derivation_old_language_transport
    (hChoice : ChoiceNatural) {oldIds : Finset Nat}
    {s : Sequent S Γ} (hOld : oldLanguage oldIds s)
    (I J : ConstVal κ S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I ρ hρ c = J ρ hρ c)
    (d : Derivation S s) : Valid J s :=
  valid_old_language_transport hOld I J hAgree (derivation_sound hChoice I d)

end QEDFV.HOL
