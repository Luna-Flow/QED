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

def Ty.typeVars : Ty → Set Nat
  | .bool => ∅
  | .ind => ∅
  | .var i => {i}
  | .arr a b => a.typeVars ∪ b.typeVars

def TypeSub.imageTypeVars (θ : TypeSub) (vars : Set Nat) : Set Nat :=
  {i | ∃ j, j ∈ vars ∧ i ∈ (θ j).typeVars}

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

@[simp] theorem Ty.typeVars_subst (a : Ty) (θ : TypeSub) :
    (a.subst θ).typeVars = TypeSub.imageTypeVars θ a.typeVars := by
  induction a with
  | bool =>
      ext i
      simp [Ty.subst, Ty.typeVars, TypeSub.imageTypeVars]
  | ind =>
      ext i
      simp [Ty.subst, Ty.typeVars, TypeSub.imageTypeVars]
  | var i =>
      ext j
      simp [Ty.subst, Ty.typeVars, TypeSub.imageTypeVars]
  | arr a b iha ihb =>
      rw [Ty.subst, Ty.typeVars, iha, ihb]
      ext i
      simp only [Set.mem_union, TypeSub.imageTypeVars, Set.mem_setOf_eq]
      constructor
      · rintro (⟨j, hja, hi⟩ | ⟨j, hjb, hi⟩)
        · exact ⟨j, Or.inl hja, hi⟩
        · exact ⟨j, Or.inr hjb, hi⟩
      · rintro ⟨j, (hja | hjb), hi⟩
        · exact Or.inl ⟨j, hja, hi⟩
        · exact Or.inr ⟨j, hjb, hi⟩

theorem TypeSub.imageTypeVars_union (θ : TypeSub) (A B : Set Nat) :
    TypeSub.imageTypeVars θ (A ∪ B) =
      TypeSub.imageTypeVars θ A ∪ TypeSub.imageTypeVars θ B := by
  ext i
  constructor
  · rintro ⟨j, (hA | hB), hi⟩
    · exact Or.inl ⟨j, hA, hi⟩
    · exact Or.inr ⟨j, hB, hi⟩
  · intro hi
    rcases hi with (⟨j, hA, hi⟩ | ⟨j, hB, hi⟩)
    · exact ⟨j, Or.inl hA, hi⟩
    · exact ⟨j, Or.inr hB, hi⟩

theorem TypeSub.imageTypeVars_image (θ σ : TypeSub) (A : Set Nat) :
    TypeSub.imageTypeVars θ (TypeSub.imageTypeVars σ A) =
      TypeSub.imageTypeVars (θ.comp σ) A := by
  ext i
  constructor
  · rintro ⟨j, ⟨k, hk, hj⟩, hi⟩
    refine ⟨k, hk, ?_⟩
    simpa [TypeSub.comp, Ty.typeVars_subst] using ⟨j, hj, hi⟩
  · rintro ⟨k, hk, hi⟩
    have hi' : i ∈ TypeSub.imageTypeVars θ ((σ k).typeVars) := by
      simpa [TypeSub.comp, Ty.typeVars_subst] using hi
    rcases hi' with ⟨j, hj, hi⟩
    exact ⟨j, ⟨k, hk, hj⟩, hi⟩

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
