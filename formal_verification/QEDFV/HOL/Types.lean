import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finset.Basic

/-! Concrete HOL carriers. Boolean values are propositions (two values by propositional
extensionality); `ind` is ℕ. Type variables range over arbitrary nonempty small types. -/
namespace QEDFV.HOL

inductive Ty where
  | bool
  | ind
  | var (id : Nat)
  | arr (dom cod : Ty)
deriving DecidableEq, Repr

abbrev TypeVal := Nat → Type
abbrev TypeSub := Nat → Ty

def Ty.denote (ρ : TypeVal) : Ty → Type
  | .bool => Prop
  | .ind => Nat
  | .var i => ρ i
  | .arr a b => a.denote ρ → b.denote ρ

def Ty.subst (θ : TypeSub) : Ty → Ty
  | .bool => .bool
  | .ind => .ind
  | .var i => θ i
  | .arr a b => .arr (a.subst θ) (b.subst θ)

abbrev TypeSub.comp (θ σ : TypeSub) : TypeSub := fun i ↦ (σ i).subst θ
abbrev TypeSub.pull (θ : TypeSub) (ρ : TypeVal) : TypeVal := fun i ↦ (θ i).denote ρ

@[simp] theorem Ty.subst_id (a : Ty) : a.subst Ty.var = a := by
  induction a <;> simp_all [Ty.subst]

@[simp] theorem Ty.subst_comp (a : Ty) (θ σ : TypeSub) :
    (a.subst σ).subst θ = a.subst (θ.comp σ) := by
  induction a <;> simp_all [Ty.subst, TypeSub.comp]

@[simp] theorem Ty.denote_subst (a : Ty) (θ : TypeSub) (ρ : TypeVal) :
    (a.subst θ).denote ρ = a.denote (θ.pull ρ) := by
  induction a <;> simp_all [Ty.subst, Ty.denote, TypeSub.pull]

def Admissible (ρ : TypeVal) : Prop := ∀ i, Nonempty (ρ i)

theorem Ty.carrier_nonempty (a : Ty) (ρ : TypeVal) (hρ : Admissible ρ) :
    Nonempty (a.denote ρ) := by
  induction a with
  | bool => exact ⟨True⟩
  | ind => exact ⟨(0 : Nat)⟩
  | var i => exact hρ i
  | arr a b _ ih =>
      rcases ih with ⟨v⟩
      exact ⟨fun _ ↦ v⟩

theorem TypeSub.pull_admissible (θ : TypeSub) (ρ : TypeVal) (hρ : Admissible ρ) :
    Admissible (θ.pull ρ) := fun i ↦ (θ i).carrier_nonempty ρ hρ

def baseTypeVal : TypeVal := fun _ ↦ Unit

theorem baseTypeVal_admissible : Admissible baseTypeVal := fun _ ↦ ⟨()⟩

theorem ind_infinity_anchor :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ := by
  refine ⟨Nat.succ_injective, ?_⟩
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.noConfusion hn

end QEDFV.HOL
