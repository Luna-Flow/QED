import QEDFV.HOL.Types

/-! Intrinsically typed De Bruijn syntax. A constant occurrence records its schema
instantiation. Variables and constants have distinct constructors. -/
namespace QEDFV.HOL

variable {κ : TyConVal}

inductive Var : List Ty → Ty → Type where
  | zero : Var (a :: Γ) a
  | succ : Var Γ a → Var (b :: Γ) a

abbrev Signature := Nat → Ty

inductive Term (S : Signature) : List Ty → Ty → Type where
  | var : Var Γ a → Term S Γ a
  | const (c : Nat) (τ : Ty) (h : (S c).IsInst τ) : Term S Γ τ
  | app : Term S Γ (.arr a b) → Term S Γ a → Term S Γ b
  | lam : Term S (a :: Γ) b → Term S Γ (.arr a b)
  | truth : Term S Γ .bool
  | falsity : Term S Γ .bool
  | conj : Term S Γ .bool → Term S Γ .bool → Term S Γ .bool
  | imp : Term S Γ .bool → Term S Γ .bool → Term S Γ .bool
  | all : Term S (a :: Γ) .bool → Term S Γ .bool
  | ex : Term S (a :: Γ) .bool → Term S Γ .bool
  | eq : Term S Γ (.arr a (.arr a .bool))
  | choice : Term S Γ (.arr (.arr a .bool) a)

def Term.typeVars : Term S Γ a → Set Nat
  | .var _ => a.typeVars
  | .const _ τ _ => τ.typeVars
  | .app f x => f.typeVars ∪ x.typeVars
  | .lam b => b.typeVars
  | .truth => ∅
  | .falsity => ∅
  | .conj p q => p.typeVars ∪ q.typeVars
  | .imp p q => p.typeVars ∪ q.typeVars
  | @Term.all _ a Γ p => a.typeVars ∪ p.typeVars
  | @Term.ex _ a Γ p => a.typeVars ∪ p.typeVars
  | .eq => a.typeVars
  | .choice => a.typeVars

/-- Every type variable occurring in any type annotation of a term, including the domain of
an unused lambda binder. Unlike `Term.typeVars` (which the closure gates use and which does
not add an unused binder's domain), this is the support on which evaluation depends. -/
def Term.annotVars : Term S Γ a → Set Nat
  | .var _ => a.typeVars
  | .const _ τ _ => τ.typeVars
  | .app f x => f.annotVars ∪ x.annotVars
  | @Term.lam _ a _ _ b => a.typeVars ∪ b.annotVars
  | .truth => ∅
  | .falsity => ∅
  | .conj p q => p.annotVars ∪ q.annotVars
  | .imp p q => p.annotVars ∪ q.annotVars
  | @Term.all _ a Γ p => a.typeVars ∪ p.annotVars
  | @Term.ex _ a Γ p => a.typeVars ∪ p.annotVars
  | .eq => a.typeVars
  | .choice => a.typeVars

/-- Type-constructor ids occurring in the types of a term: variable and binder types and
the schema instances of constants. Patterned on `Term.typeVars`. -/
def Term.tyCons : Term S Γ a → Set Nat
  | .var _ => a.tyCons
  | .const _ τ _ => τ.tyCons
  | .app f x => f.tyCons ∪ x.tyCons
  | @Term.lam _ a _ _ b => a.tyCons ∪ b.tyCons
  | .truth => ∅
  | .falsity => ∅
  | .conj p q => p.tyCons ∪ q.tyCons
  | .imp p q => p.tyCons ∪ q.tyCons
  | @Term.all _ a Γ p => a.tyCons ∪ p.tyCons
  | @Term.ex _ a Γ p => a.tyCons ∪ p.tyCons
  | .eq => a.tyCons
  | .choice => a.tyCons

/-- The annotation support contains the closure-gate support `Term.typeVars`. -/
theorem Term.typeVars_subset_annotVars (t : Term S Γ a) : t.typeVars ⊆ t.annotVars := by
  induction t with
  | var v => exact fun _ h ↦ h
  | const c τ h => exact fun _ h ↦ h
  | app f x ihf ihx => exact Set.union_subset_union ihf ihx
  | lam b ih => exact fun i h ↦ Or.inr (ih h)
  | truth => exact fun _ h ↦ h
  | falsity => exact fun _ h ↦ h
  | conj p q ihp ihq => exact Set.union_subset_union ihp ihq
  | imp p q ihp ihq => exact Set.union_subset_union ihp ihq
  | all p ih => exact Set.union_subset_union subset_rfl ih
  | ex p ih => exact Set.union_subset_union subset_rfl ih
  | eq => exact fun _ h ↦ h
  | choice => exact fun _ h ↦ h

/-- The annotation support of a term includes the type variables of its own type. -/
theorem Term.ty_annotVars_subset (t : Term S Γ a) : a.typeVars ⊆ t.annotVars := by
  induction t with
  | var v => exact fun _ h ↦ h
  | const c τ h => exact fun _ h ↦ h
  | app f x ihf ihx =>
      intro i hi
      exact Or.inl (ihf (Or.inr hi))
  | lam b ih =>
      intro i h
      simp only [Term.annotVars, Ty.typeVars, Set.mem_union] at h ⊢
      exact h.imp id fun h ↦ ih h
  | truth => exact fun i hi ↦ by cases hi
  | falsity => exact fun i hi ↦ by cases hi
  | conj p q => exact fun i hi ↦ by cases hi
  | imp p q => exact fun i hi ↦ by cases hi
  | all p => exact fun i hi ↦ by cases hi
  | ex p => exact fun i hi ↦ by cases hi
  | eq => exact fun _ h ↦ h
  | choice => exact fun _ h ↦ h

/-- The type-constructor ids of a term include those of its own type. -/
theorem Term.ty_tyCons_subset (t : Term S Γ a) : a.tyCons ⊆ t.tyCons := by
  induction t with
  | var v => exact fun _ h ↦ h
  | const c τ h => exact fun _ h ↦ h
  | app f x ihf ihx =>
      intro i hi
      exact Or.inl (ihf (Or.inr hi))
  | lam b ih =>
      intro i h
      simp only [Term.tyCons, Ty.tyCons, Set.mem_union] at h ⊢
      exact h.imp id fun h ↦ ih h
  | truth => exact fun i hi ↦ by cases hi
  | falsity => exact fun i hi ↦ by cases hi
  | conj p q => exact fun i hi ↦ by cases hi
  | imp p q => exact fun i hi ↦ by cases hi
  | all p => exact fun i hi ↦ by cases hi
  | ex p => exact fun i hi ↦ by cases hi
  | eq => exact fun _ h ↦ h
  | choice => exact fun _ h ↦ h

def Term.constIds : Term S Γ a → Finset Nat
  | .var _ => ∅
  | .const c _ _ => {c}
  | .app f x => f.constIds ∪ x.constIds
  | .lam b => b.constIds
  | .truth => ∅
  | .falsity => ∅
  | .conj p q => p.constIds ∪ q.constIds
  | .imp p q => p.constIds ∪ q.constIds
  | .all p => p.constIds
  | .ex p => p.constIds
  | .eq => ∅
  | .choice => ∅

abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a
abbrev Sub (S : Signature) (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Term S Δ a

def Ren.lift (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def Term.rename (r : Ren Γ Δ) : Term S Γ a → Term S Δ a
  | .var v => .var (r v)
  | .const c τ h => .const c τ h
  | .app f x => .app (f.rename r) (x.rename r)
  | .lam b => .lam (b.rename r.lift)
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (p.rename r) (q.rename r)
  | .imp p q => .imp (p.rename r) (q.rename r)
  | .all p => .all (p.rename r.lift)
  | .ex p => .ex (p.rename r.lift)
  | .eq => .eq
  | .choice => .choice

def Sub.lift (σ : Sub S Γ Δ) : Sub S (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => (σ v).rename Var.succ

def Term.substitute (σ : Sub S Γ Δ) : Term S Γ a → Term S Δ a
  | .var v => σ v
  | .const c τ h => .const c τ h
  | .app f x => .app (f.substitute σ) (x.substitute σ)
  | .lam b => .lam (b.substitute σ.lift)
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (p.substitute σ) (q.substitute σ)
  | .imp p q => .imp (p.substitute σ) (q.substitute σ)
  | .all p => .all (p.substitute σ.lift)
  | .ex p => .ex (p.substitute σ.lift)
  | .eq => .eq
  | .choice => .choice

def Sub.single (x : Term S Γ a) : Sub S (a :: Γ) Γ
  | _, .zero => x
  | _, .succ v => .var v

abbrev Term.equal (s t : Term S Γ a) : Term S Γ .bool := .app (.app .eq s) t

def Var.mapTypes (θ : TypeSub) : Var Γ a → Var (Γ.map (Ty.subst θ)) (a.subst θ)
  | .zero => .zero
  | .succ v => .succ (v.mapTypes θ)

def Term.instType (θ : TypeSub) : Term S Γ a →
    Term S (Γ.map (Ty.subst θ)) (a.subst θ)
  | .var v => .var (v.mapTypes θ)
  | .const c τ h => .const c (τ.subst θ) (h.inst θ)
  | .app f x => .app (f.instType θ) (x.instType θ)
  | .lam b => .lam (b.instType θ)
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (p.instType θ) (q.instType θ)
  | .imp p q => .imp (p.instType θ) (q.instType θ)
  | .all p => .all (p.instType θ)
  | .ex p => .ex (p.instType θ)
  | .eq => .eq
  | .choice => .choice

theorem Term.typeVars_cast {h : a = b} (t : Term S Γ a) :
    (h ▸ t).typeVars = t.typeVars := by
  cases h
  rfl

@[simp] theorem Term.typeVars_instType (t : Term S Γ a) (θ : TypeSub) :
    (t.instType θ).typeVars = TypeSub.imageTypeVars θ t.typeVars := by
  induction t with
  | var v =>
      simp [Term.instType, Term.typeVars, Ty.typeVars_subst]
  | const c τ h =>
      simp only [Term.instType, Term.typeVars]
      rw [Ty.typeVars_subst]
  | app f x ihf ihx =>
      simp only [Term.instType, Term.typeVars, ihf, ihx]
      exact TypeSub.imageTypeVars_union θ f.typeVars x.typeVars |>.symm
  | lam b ih =>
      simp only [Term.instType, Term.typeVars, ih]
  | truth => simp [Term.instType, Term.typeVars, TypeSub.imageTypeVars]
  | falsity => simp [Term.instType, Term.typeVars, TypeSub.imageTypeVars]
  | conj p q ihp ihq =>
      simp only [Term.instType, Term.typeVars, ihp, ihq]
      exact TypeSub.imageTypeVars_union θ p.typeVars q.typeVars |>.symm
  | imp p q ihp ihq =>
      simp only [Term.instType, Term.typeVars, ihp, ihq]
      exact TypeSub.imageTypeVars_union θ p.typeVars q.typeVars |>.symm
  | @all a Γ p ih =>
      simp only [Term.instType, Term.typeVars, Ty.typeVars_subst, ih]
      rw [TypeSub.imageTypeVars_union]
  | @ex a Γ p ih =>
      simp only [Term.instType, Term.typeVars, Ty.typeVars_subst, ih]
      rw [TypeSub.imageTypeVars_union]
  | eq =>
      simp [Term.instType, Term.typeVars, Ty.typeVars, TypeSub.imageTypeVars,
        Ty.typeVars_subst]
  | choice =>
      simp [Term.instType, Term.typeVars, Ty.typeVars, TypeSub.imageTypeVars,
        Ty.typeVars_subst]

theorem Term.tyCons_cast {h : a = b} (t : Term S Γ a) :
    (h ▸ t).tyCons = t.tyCons := by
  cases h
  rfl

@[simp] theorem Term.tyCons_instType (t : Term S Γ a) (θ : TypeSub) :
    (t.instType θ).tyCons = t.tyCons ∪ TypeSub.imageTyCons θ t.annotVars := by
  induction t with
  | var v =>
      simp [Term.instType, Term.tyCons, Term.annotVars, Ty.tyCons_subst]
  | const c τ h =>
      simp only [Term.instType, Term.tyCons, Term.annotVars]
      rw [Ty.tyCons_subst]
  | app f x ihf ihx =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ihf, ihx,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | lam b ih =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ih, Ty.tyCons_subst,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | truth => simp [Term.instType, Term.tyCons, Term.annotVars, TypeSub.imageTyCons]
  | falsity => simp [Term.instType, Term.tyCons, Term.annotVars, TypeSub.imageTyCons]
  | conj p q ihp ihq =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ihp, ihq,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | imp p q ihp ihq =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ihp, ihq,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | all p ih =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ih, Ty.tyCons_subst,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | ex p ih =>
      simp only [Term.instType, Term.tyCons, Term.annotVars, ih, Ty.tyCons_subst,
        TypeSub.imageTyCons_union]
      ext k
      simp only [Set.mem_union]
      tauto
  | eq =>
      simp only [Term.instType, Term.tyCons, Term.annotVars]
      exact Ty.tyCons_subst (.arr _ (.arr _ .bool)) θ
  | choice =>
      simp only [Term.instType, Term.tyCons, Term.annotVars]
      exact Ty.tyCons_subst (.arr (.arr _ .bool) _) θ

end QEDFV.HOL
