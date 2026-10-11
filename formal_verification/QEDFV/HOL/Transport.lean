import QEDFV.HOL.Derivation

namespace QEDFV.HOL

def Term.constIds : Term S Γ a → Finset Nat
  | .var _ => ∅
  | .const c _ => {c}
  | .app f x => f.constIds ∪ x.constIds
  | .lam b => b.constIds
  | .eq => ∅
  | .choice => ∅

theorem Term.eval_agree (t : Term S Γ a) (I J : ConstVal S)
    (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ)
    (hAgree : ∀ c, c ∈ t.constIds → ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I ρ hρ c = J ρ hρ c) :
    t.eval I ρ hρ η = t.eval J ρ hρ η := by
  induction t with
  | var v => rfl
  | const c σ =>
      have hc := hAgree c (by simp [Term.constIds])
        (σ.pull ρ) (σ.pull_admissible ρ hρ)
      simp only [Term.eval]
      rw [hc]
  | app f x ihf ihx =>
      simp only [Term.eval]
      rw [ihf η (by
        intro c hc ρ' hρ'
        exact hAgree c (by simp [Term.constIds, hc]) ρ' hρ'),
        ihx η (by
          intro c hc ρ' hρ'
          exact hAgree c (by simp [Term.constIds, hc]) ρ' hρ')]
  | lam b ih =>
      simp only [Term.eval]
      funext x
      apply ih
      intro c hc ρ' hρ'
      exact hAgree c (by simpa [Term.constIds] using hc) ρ' hρ'
  | eq => rfl
  | choice => rfl

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

theorem valid_transport {s : Sequent S Γ} (I J : ConstVal S)
    (hAgree : ∀ c, c ∈ s.constIds → ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I ρ hρ c = J ρ hρ c) (hValid : Valid I s) :
    Valid J s := by
  intro ρ hρ η hh
  have hHypI : ∀ h, h ∈ s.hyps → h.eval I ρ hρ η := by
    intro h hhmem
    have heq := Term.eval_agree h I J ρ hρ η (by
      intro c hc ρ' hρ'
      exact hAgree c (Sequent.mem_constIds_hyp hhmem hc) ρ' hρ')
    rw [heq]
    exact hh h hhmem
  have hConclI := hValid ρ hρ η hHypI
  have heq := Term.eval_agree s.concl I J ρ hρ η (by
    intro c hc ρ' hρ'
    exact hAgree c (Sequent.mem_constIds_concl hc) ρ' hρ')
  rw [← heq]
  exact hConclI

def oldLanguage (oldIds : Finset Nat) (s : Sequent S Γ) : Prop :=
  s.constIds ⊆ oldIds

theorem valid_old_language_transport {oldIds : Finset Nat} {s : Sequent S Γ}
    (hOld : oldLanguage oldIds s) (I J : ConstVal S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I ρ hρ c = J ρ hρ c) (hValid : Valid I s) :
    Valid J s := by
  apply valid_transport I J
  intro c hc ρ hρ
  exact hAgree c (hOld hc) ρ hρ
  exact hValid

theorem valid_old_language_iff {oldIds : Finset Nat} {s : Sequent S Γ}
    (hOld : oldLanguage oldIds s) (I J : ConstVal S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I ρ hρ c = J ρ hρ c) :
    Valid I s ↔ Valid J s := by
  constructor
  · exact valid_old_language_transport hOld I J hAgree
  · intro hValid
    apply valid_old_language_transport hOld J I
    intro c hc ρ hρ
    exact (hAgree c hc ρ hρ).symm
    exact hValid

theorem derivation_old_language_transport
    (hChoice : ChoiceNatural) {oldIds : Finset Nat}
    {s : Sequent S Γ} (hOld : oldLanguage oldIds s)
    (I J : ConstVal S)
    (hAgree : ∀ c, c ∈ oldIds → ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I ρ hρ c = J ρ hρ c)
    (d : Derivation S s) : Valid J s :=
  valid_old_language_transport hOld I J hAgree (derivation_sound hChoice I d)

end QEDFV.HOL
