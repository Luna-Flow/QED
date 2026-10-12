import QEDFV.HOL.Rules

namespace QEDFV.HOL

theorem heq_app_cast {α β γ δ : Sort u}
    {f : α → β} {g : γ → δ} {x : α} {y : γ}
    (hα : α = γ) (hβ : β = δ) (hf : f ≍ g) (hx : x ≍ y) :
    f x ≍ g y := by
  cases hα
  cases hβ
  apply heq_of_eq
  exact congrArg₂ (fun k z ↦ k z) (eq_of_heq hf) (eq_of_heq hx)

theorem heq_fun_cast {α : Sort u} {β : Sort u} {γ : Sort u} {δ : Sort u}
    {f : α → β} {g : γ → δ} (hα : α = γ) (hβ : β = δ)
    (h : ∀ x : α, f x ≍ g (cast hα x)) : f ≍ g := by
  cases hα
  cases hβ
  apply heq_of_eq
  funext x
  exact eq_of_heq (h x)

theorem eq_natural {A B : Type} (h : A = B) :
    HEq (fun x y : A => x = y) (fun x y : B => x = y) := by
  cases h
  rfl

theorem eval_term_cast {S : Signature} {Γ : List Ty} {a b : Ty}
    (I : ConstVal S) (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ)
    (h : a = b) (t : Term S Γ a) :
    HEq ((h ▸ t).eval I ρ hρ η) (t.eval I ρ hρ η) := by
  cases h
  rfl

theorem constVal_heq {S : Signature} (I : ConstVal S) {ρ σ : TypeVal}
    (h : ρ = σ) (hρ : Admissible ρ) (hσ : Admissible σ) (c : Nat) :
    HEq (I ρ hρ c) (I σ hσ c) := by
  cases h
  rfl

def Env.instPull {ρ : TypeVal} {Γ : List Ty} (θ : TypeSub)
    (η : Env ρ (Γ.map (Ty.subst θ))) :
    Env (θ.pull ρ) Γ := fun a v ↦ cast (a.denote_subst θ ρ) (η (a.subst θ) (v.mapTypes θ))

theorem Env.instPull_extend {ρ : TypeVal} {Γ : List Ty} (θ : TypeSub)
    (η : Env ρ (Γ.map (Ty.subst θ)))
    (x : Ty.denote ρ (a.subst θ)) :
    Env.instPull θ (Env.extend (a := a.subst θ) η x) =
      Env.extend (a := a) (Env.instPull θ η) (cast (a.denote_subst θ ρ) x) := by
  funext b v
  cases v <;> rfl

structure ChoiceNatural : Prop where
  choice_natural : ∀ (θ : TypeSub) (ρ : TypeVal) (hρ : Admissible ρ) (a : Ty),
    letI : Nonempty (Ty.denote ρ (a.subst θ)) := (a.subst θ).carrier_nonempty ρ hρ
    letI : Nonempty (Ty.denote (θ.pull ρ) a) := a.carrier_nonempty (θ.pull ρ)
      (θ.pull_admissible ρ hρ)
    HEq (select (Ty.denote ρ (a.subst θ))) (select (Ty.denote (θ.pull ρ) a))

theorem select_heq_of_type_eq {A B : Type} [Nonempty A] [Nonempty B]
    (h : A = B) : HEq (select A) (select B) := by
  cases h
  rfl

theorem select_natural : ChoiceNatural := by
  constructor
  intro θ ρ hρ a
  letI : Nonempty (Ty.denote ρ (a.subst θ)) := (a.subst θ).carrier_nonempty ρ hρ
  letI : Nonempty (Ty.denote (θ.pull ρ) a) :=
    a.carrier_nonempty (θ.pull ρ) (θ.pull_admissible ρ hρ)
  exact select_heq_of_type_eq (Ty.denote_subst a θ ρ)

theorem Term.eval_instType
    (hChoice : ChoiceNatural)
    (I : ConstVal S) (ρ : TypeVal) (hρ : Admissible ρ)
    (t : Term S Γ a) (θ : TypeSub)
    (η : Env ρ (Γ.map (Ty.subst θ))) :
    HEq ((t.instType θ).eval I ρ hρ η)
      (t.eval I (θ.pull ρ) (θ.pull_admissible ρ hρ) (Env.instPull θ η)) := by
  induction t with
  | var v =>
      exact (cast_heq (Ty.denote_subst _ θ ρ) (η _ (v.mapTypes θ))).symm
  | const c σ =>
      have hpull : (θ.comp σ).pull ρ = σ.pull (θ.pull ρ) := by
        funext i
        simp [TypeSub.pull, TypeSub.comp, Ty.denote_subst]
      simp only [Term.instType, Term.eval]
      have hcast := eval_term_cast I ρ hρ η
        (Ty.subst_comp (S c) θ σ).symm (.const c (θ.comp σ))
      have hraw : HEq
          ((Term.const c (θ.comp σ)).eval I ρ hρ η)
          ((Term.const c σ).eval I (θ.pull ρ) (θ.pull_admissible ρ hρ)
            (Env.instPull θ η)) := by
        simp only [Term.eval]
        have hi := constVal_heq I hpull
          ((θ.comp σ).pull_admissible ρ hρ)
          (σ.pull_admissible (θ.pull ρ) (θ.pull_admissible ρ hρ)) c
        exact (cast_heq _ _).trans (hi.trans (cast_heq _ _).symm)
      exact hcast.trans hraw
  | @app Γ a b f x ihf ihx =>
      simp only [Term.instType, Term.eval]
      have hf := ihf η
      have hx := ihx η
      exact heq_app_cast (Ty.denote_subst a θ ρ) (Ty.denote_subst b θ ρ) hf hx
  | @lam a Γ b body ih =>
      simp only [Term.instType, Term.eval]
      apply heq_fun_cast (a.denote_subst θ ρ) (b.denote_subst θ ρ)
      intro x
      have hb := ih (Env.extend η x)
      rw [Env.instPull_extend] at hb
      exact hb
  | truth => exact heq_of_eq rfl
  | falsity => exact heq_of_eq rfl
  | conj p q ihp ihq =>
      simp only [Term.instType, Term.eval]
      have hp := ihp η
      have hq := ihq η
      rw [eq_of_heq hp, eq_of_heq hq]
  | imp p q ihp ihq =>
      simp only [Term.instType, Term.eval]
      have hp := ihp η
      have hq := ihq η
      rw [eq_of_heq hp, eq_of_heq hq]
  | @all a Γ p ih =>
      simp only [Term.instType, Term.eval]
      apply heq_of_eq
      apply propext
      constructor
      · intro h x
        let x' : Ty.denote ρ (a.subst θ) :=
          cast (Ty.denote_subst a θ ρ).symm x
        have hb := ih (Env.extend η x')
        rw [Env.instPull_extend] at hb
        simpa [x'] using (eq_of_heq hb).mp (h x')
      · intro h x
        let x' : Ty.denote ρ (a.subst θ) := x
        have hb := ih (Env.extend η x')
        rw [Env.instPull_extend] at hb
        simpa [x'] using (eq_of_heq hb).mpr (h (cast (Ty.denote_subst a θ ρ) x'))
  | @ex a Γ p ih =>
      simp only [Term.instType, Term.eval]
      apply heq_of_eq
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        have hb := ih (Env.extend η x)
        rw [Env.instPull_extend] at hb
        exact ⟨cast (Ty.denote_subst a θ ρ) x, (eq_of_heq hb).mp hx⟩
      · rintro ⟨x, hx⟩
        let x' : Ty.denote ρ (a.subst θ) :=
          cast (Ty.denote_subst a θ ρ).symm x
        have hb := ih (Env.extend η x')
        rw [Env.instPull_extend] at hb
        exact ⟨x', (eq_of_heq hb).mpr (by simpa [x'] using hx)⟩
  | @eq Γ a =>
      simpa only [Term.instType, Term.eval] using eq_natural (a.denote_subst θ ρ)
  | @choice Γ a =>
      exact hChoice.choice_natural θ ρ hρ a

def typeSubstSequent (θ : TypeSub) (s : Sequent S Γ) :
    Sequent S (Γ.map (Ty.subst θ)) :=
  { hyps := s.hyps.map (fun h ↦ h.instType θ)
  , concl := s.concl.instType θ }

theorem valid_inst_type
    (hChoice : ChoiceNatural) (I : ConstVal S) (θ : TypeSub)
    (s : Sequent S Γ) (hValid : Valid I s) :
    Valid I (typeSubstSequent θ s) := by
  intro ρ hρ η hh
  change (s.concl.instType θ).eval I ρ hρ η
  have hEval := Term.eval_instType hChoice I ρ hρ s.concl θ η
  have hOrig := hValid (θ.pull ρ) (θ.pull_admissible ρ hρ) (Env.instPull θ η) (by
    intro h hh'
    have h0valid := hh (h.instType θ) (List.mem_map.mpr ⟨h, hh', rfl⟩)
    have hEvalHyp := Term.eval_instType hChoice I ρ hρ h θ η
    rw [eq_of_heq hEvalHyp] at h0valid
    exact h0valid)
  rw [eq_of_heq hEval]
  exact hOrig

end QEDFV.HOL
