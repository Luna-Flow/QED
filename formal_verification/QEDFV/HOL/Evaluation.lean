import QEDFV.HOL.Terms

/-! Evaluation into actual carriers. None of the evaluation, substitution or beta
laws is a field of the model. Polymorphic constants are interpreted at their schema. -/
namespace QEDFV.HOL

variable {κ : TyConVal}

abbrev Env κ (ρ : TypeVal) (Γ : List Ty) := ∀ (a : Ty), Var Γ a → Ty.denote κ ρ a
abbrev ConstVal (κ : TyConVal) (S : Signature) :=
  ∀ (ρ : TypeVal), Admissible κ ρ → ∀ c, (S c).denote κ ρ

noncomputable def canonicalConstVal (κ : TyConVal) (S : Signature) : ConstVal κ S :=
  fun ρ hρ c ↦ Classical.choice ((S c).carrier_nonempty κ ρ hρ)

def Env.extend (η : Env κ ρ Γ) (x : Ty.denote κ ρ a) : Env κ ρ (a :: Γ)
  | _, .zero => x
  | _, .succ v => η _ v

def Env.pull (η : Env κ ρ Δ) (r : Ren Γ Δ) : Env κ ρ Γ := fun _ v ↦ η _ (r v)

noncomputable def select (α : Type) [Nonempty α] (p : α → Prop) : α := by
  classical
  exact if h : ∃ x, p x then Classical.choose h else Classical.choice inferInstance

theorem select_spec (α : Type) [Nonempty α] (p : α → Prop) (h : ∃ x, p x) :
    p (select α p) := by
  simp only [select, dif_pos h]
  exact Classical.choose_spec h

noncomputable def Term.eval (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (η : Env κ ρ Γ) : Term S Γ a → Ty.denote κ ρ a
  | .var v => η _ v
  | .const c τ h =>
      cast (((S c).denote_subst κ (Ty.constSub (S c) τ h) ρ).symm.trans
          (congrArg (Ty.denote κ ρ) (Ty.constSub_spec (S c) τ h)))
        (I ((Ty.constSub (S c) τ h).pull κ ρ)
          ((Ty.constSub (S c) τ h).pull_admissible κ ρ hρ) c)
  | .app f x => f.eval I ρ hρ η (x.eval I ρ hρ η)
  | .lam b => fun x ↦ b.eval I ρ hρ (η.extend x)
  | .truth => True
  | .falsity => False
  | .conj p q => p.eval I ρ hρ η ∧ q.eval I ρ hρ η
  | .imp p q => p.eval I ρ hρ η → q.eval I ρ hρ η
  | .all p => ∀ x, p.eval I ρ hρ (η.extend x)
  | .ex p => ∃ x, p.eval I ρ hρ (η.extend x)
  | .eq => fun x y ↦ x = y
  | @Term.choice _ _ a =>
      have : Nonempty (Ty.denote κ ρ a) := a.carrier_nonempty κ ρ hρ
      select (Ty.denote κ ρ a)

@[simp] theorem Term.eval_truth (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) :
    (Term.truth : Term S Γ .bool).eval I ρ hρ η = True := rfl

@[simp] theorem Term.eval_falsity (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) :
    (Term.falsity : Term S Γ .bool).eval I ρ hρ η = False := rfl

@[simp] theorem Term.eval_conj (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) (p q : Term S Γ .bool) :
    (Term.conj p q).eval I ρ hρ η =
      (p.eval I ρ hρ η ∧ q.eval I ρ hρ η) := rfl

@[simp] theorem Term.eval_imp (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) (p q : Term S Γ .bool) :
    (Term.imp p q).eval I ρ hρ η =
      (p.eval I ρ hρ η → q.eval I ρ hρ η) := rfl

@[simp] theorem Term.eval_all (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) (p : Term S (a :: Γ) .bool) :
    (Term.all p).eval I ρ hρ η =
      (∀ x, p.eval I ρ hρ (η.extend x)) := rfl

@[simp] theorem Term.eval_ex (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) (p : Term S (a :: Γ) .bool) :
    (Term.ex p).eval I ρ hρ η =
      (∃ x, p.eval I ρ hρ (η.extend x)) := rfl

@[simp] theorem Term.eval_equal (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (η : Env κ ρ Γ) (s t : Term S Γ a) :
    (s.equal t).eval I ρ hρ η = (s.eval I ρ hρ η = t.eval I ρ hρ η) := rfl

theorem Env.pull_extend (η : Env κ ρ Δ) (r : Ren Γ Δ) (x : Ty.denote κ ρ a) :
    Env.pull (Env.extend (a := a) η x) r.lift = Env.extend (a := a) (Env.pull η r) x := by
  funext b v
  cases v <;> rfl

theorem Term.eval_rename (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (t : Term S Γ a) (r : Ren Γ Δ) (η : Env κ ρ Δ) :
    (t.rename r).eval I ρ hρ η = t.eval I ρ hρ (Env.pull η r) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [rename, eval, ihf, ihx]
  | lam b ih =>
      funext x
      simpa only [rename, eval, Env.pull_extend] using ih r.lift (Env.extend η x)
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [rename, eval, ihp, ihq]
  | imp p q ihp ihq => simp only [rename, eval, ihp, ihq]
  | all p ih =>
      simp only [rename, eval]
      apply propext
      constructor
      · intro h x
        have hi := ih r.lift (Env.extend η x)
        rw [Env.pull_extend] at hi
        exact hi.mp (h x)
      · intro h x
        have ihx := ih r.lift (Env.extend η x)
        rw [Env.pull_extend] at ihx
        exact ihx.mpr (h x)
  | ex p ih =>
      simp only [rename, eval]
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        have hi := ih r.lift (Env.extend η x)
        rw [Env.pull_extend] at hi
        exact ⟨x, hi.mp hx⟩
      · rintro ⟨x, hx⟩
        have hi := ih r.lift (Env.extend η x)
        rw [Env.pull_extend] at hi
        exact ⟨x, hi.mpr hx⟩
  | eq => rfl
  | choice => rfl

noncomputable def Sub.evalSubst (σ : Sub S Γ Δ) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Δ) : Env κ ρ Γ := fun _ v ↦ (σ v).eval I ρ hρ η

theorem Sub.eval_lift (σ : Sub S Γ Δ) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Δ) (x : Ty.denote κ ρ a) :
    Sub.evalSubst σ.lift I ρ hρ (Env.extend (a := a) η x) =
      Env.extend (a := a) (Sub.evalSubst σ I ρ hρ η) x := by
  funext b v
  cases v with
  | zero => rfl
  | succ v =>
      simp only [Sub.evalSubst, Sub.lift, Term.eval_rename]
      rfl

theorem Term.eval_substitute (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (t : Term S Γ a) (σ : Sub S Γ Δ) (η : Env κ ρ Δ) :
    (t.substitute σ).eval I ρ hρ η = t.eval I ρ hρ (Sub.evalSubst σ I ρ hρ η) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c τ h => rfl
  | app f x ihf ihx => simp only [substitute, eval, ihf, ihx]
  | lam b ih =>
      funext x
      simpa only [substitute, eval, Sub.eval_lift] using ih σ.lift (Env.extend η x)
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [substitute, eval, ihp, ihq]
  | imp p q ihp ihq => simp only [substitute, eval, ihp, ihq]
  | all p ih =>
      simp only [substitute, eval]
      apply propext
      constructor
      · intro h x
        have hi := ih σ.lift (Env.extend η x)
        rw [Sub.eval_lift] at hi
        exact hi.mp (h x)
      · intro h x
        have ihx := ih σ.lift (Env.extend η x)
        rw [Sub.eval_lift] at ihx
        exact ihx.mpr (h x)
  | ex p ih =>
      simp only [substitute, eval]
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        have hi := ih σ.lift (Env.extend η x)
        rw [Sub.eval_lift] at hi
        exact ⟨x, hi.mp hx⟩
      · rintro ⟨x, hx⟩
        have hi := ih σ.lift (Env.extend η x)
        rw [Sub.eval_lift] at hi
        exact ⟨x, hi.mpr hx⟩
  | eq => rfl
  | choice => rfl

theorem Sub.eval_single (x : Term S Γ a) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (η : Env κ ρ Γ) :
    Sub.evalSubst (Sub.single x) I ρ hρ η = Env.extend (a := a) η (x.eval I ρ hρ η) := by
  funext (b : Ty) v
  cases v <;> rfl

theorem Term.eval_beta (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (η : Env κ ρ Γ) (b : Term S (a :: Γ) c) (x : Term S Γ a) :
    (Term.app (.lam b) x).eval I ρ hρ η =
      (b.substitute (Sub.single x)).eval I ρ hρ η := by
  rw [eval_substitute, Sub.eval_single]
  rfl

end QEDFV.HOL
