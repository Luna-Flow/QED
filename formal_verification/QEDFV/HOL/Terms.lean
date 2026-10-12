import QEDFV.HOL.Types

/-! Intrinsically typed De Bruijn syntax. A constant occurrence records its schema
instantiation. Variables and constants have distinct constructors. -/
namespace QEDFV.HOL

inductive Var : List Ty → Ty → Type where
  | zero : Var (a :: Γ) a
  | succ : Var Γ a → Var (b :: Γ) a

abbrev Signature := Nat → Ty

inductive Term (S : Signature) : List Ty → Ty → Type where
  | var : Var Γ a → Term S Γ a
  | const (c : Nat) (σ : TypeSub) : Term S Γ ((S c).subst σ)
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
  | .const c σ => ((S c).subst σ).typeVars
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

abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a
abbrev Sub (S : Signature) (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Term S Δ a

def Ren.lift (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def Term.rename (r : Ren Γ Δ) : Term S Γ a → Term S Δ a
  | .var v => .var (r v)
  | .const c σ => .const c σ
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
  | .const c θ => .const c θ
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
  | .const c σ => (Ty.subst_comp (S c) θ σ).symm ▸ .const c (θ.comp σ)
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
  | const c σ =>
      simp only [Term.instType]
      rw [Term.typeVars_cast]
      change ((S c).subst (θ.comp σ)).typeVars =
        TypeSub.imageTypeVars θ ((S c).subst σ).typeVars
      rw [Ty.typeVars_subst, Ty.typeVars_subst, TypeSub.imageTypeVars_image]
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

end QEDFV.HOL
