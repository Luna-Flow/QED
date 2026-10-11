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
  | eq : Term S Γ (.arr a (.arr a .bool))
  | choice : Term S Γ (.arr (.arr a .bool) a)

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
  | .eq => .eq
  | .choice => .choice

end QEDFV.HOL
