import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finset.Basic

/-! Concrete HOL carriers. Boolean values are propositions (two values by propositional
extensionality); `ind` is ℕ. Type variables range over arbitrary nonempty small types.
A type-constructor node `Ty.con k n args` is interpreted by an explicit constructor
interpretation `TyConVal`; the core calculus is sound for every such interpretation. -/
namespace QEDFV.HOL

inductive Ty where
  | bool
  | ind
  | var (id : Nat)
  | arr (dom cod : Ty)
  /-- Application of the type constructor with id `k` and arity `n`. Arity correctness
  of a particular `k` is a side condition of later gates, not part of `Ty`. -/
  | con (k n : Nat) (args : Fin n → Ty)

/-- Interpretation of type-constructor nodes: a carrier for each constructor id, arity and
tuple of argument carriers. -/
structure TyConVal where
  carrier : Nat → (n : Nat) → (Fin n → Type) → Type

abbrev TypeVal := Nat → Type
abbrev TypeSub := Nat → Ty

def Ty.typeVars : Ty → Set Nat
  | .bool => ∅
  | .ind => ∅
  | .var i => {i}
  | .arr a b => a.typeVars ∪ b.typeVars
  | .con _ _ args => {i | ∃ j, i ∈ (args j).typeVars}

/-- Type-constructor ids occurring in a type. -/
def Ty.tyCons : Ty → Set Nat
  | .bool => ∅
  | .ind => ∅
  | .var _ => ∅
  | .arr a b => a.tyCons ∪ b.tyCons
  | .con k _ args => {k} ∪ {i | ∃ j, i ∈ (args j).tyCons}

/-- Two constructor interpretations have equal carriers on every constructor id in `C`
(at every arity and every tuple of argument carriers). -/
def TyConVal.AgreeOn (κ : TyConVal) (C : Set Nat) (κ' : TyConVal) : Prop :=
  ∀ k, k ∈ C → ∀ (n : Nat) (as : Fin n → Type), κ.carrier k n as = κ'.carrier k n as

/-- Every constructor carrier is nonempty whenever its argument carriers are. -/
def TyConVal.IsAdmissible (κ : TyConVal) : Prop :=
  ∀ (k n : Nat) (as : Fin n → Type), (∀ j, Nonempty (as j)) → Nonempty (κ.carrier k n as)

def TypeSub.imageTypeVars (θ : TypeSub) (vars : Set Nat) : Set Nat :=
  {i | ∃ j, j ∈ vars ∧ i ∈ (θ j).typeVars}

def Ty.denote (κ : TyConVal) (ρ : TypeVal) : Ty → Type
  | .bool => Prop
  | .ind => Nat
  | .var i => ρ i
  | .arr a b => a.denote κ ρ → b.denote κ ρ
  | .con k n args => κ.carrier k n (fun j ↦ (args j).denote κ ρ)

def Ty.subst (θ : TypeSub) : Ty → Ty
  | .bool => .bool
  | .ind => .ind
  | .var i => θ i
  | .arr a b => .arr (a.subst θ) (b.subst θ)
  | .con k n args => .con k n (fun j ↦ (args j).subst θ)

abbrev TypeSub.comp (θ σ : TypeSub) : TypeSub := fun i ↦ (σ i).subst θ
abbrev TypeSub.pull (θ : TypeSub) (κ : TyConVal) (ρ : TypeVal) : TypeVal :=
  fun i ↦ (θ i).denote κ ρ

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
  | con k n args ih =>
      ext i
      simp only [Ty.subst, Ty.typeVars, ih, TypeSub.imageTypeVars, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, l, hl, hi⟩
        exact ⟨l, ⟨j, hl⟩, hi⟩
      · rintro ⟨l, ⟨j, hl⟩, hi⟩
        exact ⟨j, l, hl, hi⟩

/-- Constructor ids occurring in the images of the variables in `vars`. -/
def TypeSub.imageTyCons (θ : TypeSub) (vars : Set Nat) : Set Nat :=
  {k | ∃ j, j ∈ vars ∧ k ∈ (θ j).tyCons}

@[simp] theorem Ty.tyCons_subst (a : Ty) (θ : TypeSub) :
    (a.subst θ).tyCons = a.tyCons ∪ TypeSub.imageTyCons θ a.typeVars := by
  induction a with
  | bool => ext i; simp [Ty.subst, Ty.tyCons, Ty.typeVars, TypeSub.imageTyCons]
  | ind => ext i; simp [Ty.subst, Ty.tyCons, Ty.typeVars, TypeSub.imageTyCons]
  | var i => ext j; simp [Ty.subst, Ty.tyCons, Ty.typeVars, TypeSub.imageTyCons]
  | arr a b iha ihb =>
      rw [Ty.subst, Ty.tyCons, iha, ihb]
      ext i
      simp only [Set.mem_union, TypeSub.imageTyCons, Ty.typeVars, Set.mem_setOf_eq]
      constructor
      · rintro ((h | ⟨j, hj, hi⟩) | (h | ⟨j, hj, hi⟩))
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨j, Or.inl hj, hi⟩
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨j, Or.inr hj, hi⟩
      · rintro ((h | h) | ⟨j, (hj | hj), hi⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr ⟨j, hj, hi⟩)
        · exact Or.inr (Or.inr ⟨j, hj, hi⟩)
  | con k n args ih =>
      ext i
      simp only [Ty.subst, Ty.tyCons, ih, TypeSub.imageTyCons, Ty.typeVars, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨j, h | ⟨l, hl, hi⟩⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨j, h⟩)
        · exact Or.inr ⟨l, ⟨j, hl⟩, hi⟩
      · rintro ((h | ⟨j, hj⟩) | ⟨l, ⟨j, hl⟩, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, Or.inl hj⟩
        · exact Or.inr ⟨j, Or.inr ⟨l, hl, hi⟩⟩

theorem TypeSub.imageTyCons_union (θ : TypeSub) (A B : Set Nat) :
    TypeSub.imageTyCons θ (A ∪ B) =
      TypeSub.imageTyCons θ A ∪ TypeSub.imageTyCons θ B := by
  ext i
  constructor
  · rintro ⟨j, (hA | hB), hi⟩
    · exact Or.inl ⟨j, hA, hi⟩
    · exact Or.inr ⟨j, hB, hi⟩
  · rintro (⟨j, hA, hi⟩ | ⟨j, hB, hi⟩)
    · exact ⟨j, Or.inl hA, hi⟩
    · exact ⟨j, Or.inr hB, hi⟩

theorem TypeSub.imageTyCons_comp (θ σ : TypeSub) (A : Set Nat) :
    TypeSub.imageTyCons (fun i ↦ (σ i).subst θ) A =
      TypeSub.imageTyCons σ A ∪ TypeSub.imageTyCons θ (TypeSub.imageTypeVars σ A) := by
  ext k
  simp only [TypeSub.imageTyCons, TypeSub.imageTypeVars, Ty.tyCons_subst, Set.mem_union,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, (hk | ⟨l, hl, hk⟩)⟩
    · exact Or.inl ⟨j, hj, hk⟩
    · exact Or.inr ⟨l, ⟨j, hj, hl⟩, hk⟩
  · rintro (⟨j, hj, hk⟩ | ⟨l, ⟨j, hj, hl⟩, hk⟩)
    · exact ⟨j, hj, Or.inl hk⟩
    · exact ⟨j, hj, Or.inr ⟨l, hl, hk⟩⟩

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

theorem Ty.subst_congr (a : Ty) {σ σ' : TypeSub} (h : ∀ i, i ∈ a.typeVars → σ i = σ' i) :
    a.subst σ = a.subst σ' := by
  induction a with
  | bool => rfl
  | ind => rfl
  | var i => exact h i (by simp [Ty.typeVars])
  | arr a b iha ihb =>
      simp only [Ty.subst]
      rw [iha (fun i hi ↦ h i (Or.inl hi)), ihb (fun i hi ↦ h i (Or.inr hi))]
  | con j m args ih =>
      simp only [Ty.subst]
      congr 1
      funext i
      exact ih i (fun i' hi ↦ h i' ⟨i, hi⟩)

/-- A substitution is determined on the type variables of `a` by the instance `a.subst σ`. -/
theorem Ty.subst_unique (a : Ty) {σ σ' : TypeSub} (h : a.subst σ = a.subst σ') :
    ∀ i, i ∈ a.typeVars → σ i = σ' i := by
  induction a with
  | bool => intro i hi; simp [Ty.typeVars] at hi
  | ind => intro i hi; simp [Ty.typeVars] at hi
  | var i => intro j hj; simp [Ty.typeVars] at hj; subst hj; simpa [Ty.subst] using h
  | arr a b iha ihb =>
      simp only [Ty.subst, Ty.arr.injEq] at h
      intro i hi
      rcases hi with hi | hi
      · exact iha h.1 i hi
      · exact ihb h.2 i hi
  | con j m args ih =>
      simp only [Ty.subst, Ty.con.injEq] at h
      obtain ⟨_, _, hargs⟩ := h
      intro i hi
      obtain ⟨j', hj'⟩ := hi
      exact ih j' (congrFun (eq_of_heq hargs) j') i hj'

@[simp] theorem Ty.denote_subst (a : Ty) (κ : TyConVal) (θ : TypeSub) (ρ : TypeVal) :
    (a.subst θ).denote κ ρ = a.denote κ (θ.pull κ ρ) := by
  induction a <;> simp_all [Ty.subst, Ty.denote, TypeSub.pull]

/-- Denotation of a type depends only on the carriers of the type variables in `V` and of the
constructors in `C` that occur in it. -/
theorem Ty.denote_congr_gen (a : Ty) {κ κ' : TyConVal} {ρ ρ' : TypeVal} (V C : Set Nat)
    (hV : ∀ i, i ∈ V → ρ i = ρ' i) (hC : κ.AgreeOn C κ')
    (hv : a.typeVars ⊆ V) (hc : a.tyCons ⊆ C) : a.denote κ ρ = a.denote κ' ρ' := by
  induction a with
  | bool => rfl
  | ind => rfl
  | var i => exact hV i (hv (by simp [Ty.typeVars]))
  | arr a b iha ihb =>
      simp only [Ty.denote]
      rw [iha (fun i hi ↦ hv (Or.inl hi)) (fun i hi ↦ hc (Or.inl hi)),
        ihb (fun i hi ↦ hv (Or.inr hi)) (fun i hi ↦ hc (Or.inr hi))]
  | con k n args ih =>
      simp only [Ty.denote]
      have hargs : (fun j ↦ (args j).denote κ ρ) = (fun j ↦ (args j).denote κ' ρ') :=
        funext fun j ↦ ih j (fun i hi ↦ hv ⟨j, hi⟩) (fun i hi ↦ hc (Or.inr ⟨j, hi⟩))
      rw [hargs]
      exact hC k (hc (Or.inl rfl)) n _

/-- Denotation depends only on the carriers of the constructors occurring in the type. -/
theorem Ty.denote_congr (a : Ty) {κ κ' : TyConVal} (ρ : TypeVal)
    (hC : κ.AgreeOn a.tyCons κ') : a.denote κ ρ = a.denote κ' ρ :=
  a.denote_congr_gen (ρ := ρ) (ρ' := ρ) Set.univ a.tyCons (fun _ _ ↦ rfl) hC
    (Set.subset_univ _) subset_rfl

/-- Denotation depends only on the type variables occurring in the type. -/
theorem Ty.denote_congr_vars (a : Ty) (κ : TyConVal) {ρ ρ' : TypeVal}
    (h : ∀ i, i ∈ a.typeVars → ρ i = ρ' i) : a.denote κ ρ = a.denote κ ρ' :=
  a.denote_congr_gen (κ := κ) (κ' := κ) a.typeVars Set.univ h (fun _ _ _ _ ↦ rfl)
    subset_rfl (Set.subset_univ _)

/-- Admissible interpretations: nonempty carriers for type variables, and constructor
carriers that are nonempty whenever all their argument carriers are. A constructor
interpretation that violates the second clause admits no `ρ`, so every sequent is vacuously
valid under it. -/
structure Admissible (κ : TyConVal) (ρ : TypeVal) : Prop where
  var : ∀ i, Nonempty (ρ i)
  con : ∀ (k n : Nat) (as : Fin n → Type), (∀ j, Nonempty (as j)) →
    Nonempty (κ.carrier k n as)

theorem Ty.carrier_nonempty (a : Ty) (κ : TyConVal) (ρ : TypeVal) (hρ : Admissible κ ρ) :
    Nonempty (a.denote κ ρ) := by
  induction a with
  | bool => exact ⟨True⟩
  | ind => exact ⟨(0 : Nat)⟩
  | var i => exact hρ.var i
  | arr a b _ ih =>
      rcases ih with ⟨v⟩
      exact ⟨fun _ ↦ v⟩
  | con k n args ih => exact hρ.con k n _ ih

theorem TypeSub.pull_admissible (θ : TypeSub) (κ : TyConVal) (ρ : TypeVal)
    (hρ : Admissible κ ρ) : Admissible κ (θ.pull κ ρ) :=
  ⟨fun i ↦ (θ i).carrier_nonempty κ ρ hρ, hρ.con⟩

/-- The default constructor interpretation: every constructor denotes `PUnit`. -/
def defaultTyCon : TyConVal := ⟨fun _ _ _ ↦ PUnit⟩

def baseTypeVal : TypeVal := fun _ ↦ Unit

theorem defaultTyCon_baseTypeVal_admissible : Admissible defaultTyCon baseTypeVal :=
  ⟨fun _ ↦ ⟨()⟩, fun _ _ _ _ ↦ ⟨PUnit.unit⟩⟩

theorem baseTypeVal_admissible : Admissible defaultTyCon baseTypeVal :=
  defaultTyCon_baseTypeVal_admissible

theorem ind_infinity_anchor :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ := by
  refine ⟨Nat.succ_injective, ?_⟩
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.noConfusion hn

/-! ### Instances of a schema

A constant occurrence records the *type* at which the constant is used, together with the fact
that this type is an instance of the constant's schema. The instance substitution is determined
on the type variables of the schema, so it is not part of the syntax. -/

/-- `τ` is an instance of the schema `s`. -/
def Ty.IsInst (s τ : Ty) : Prop := ∃ σ : TypeSub, s.subst σ = τ

theorem Ty.IsInst.inst {s τ : Ty} (h : s.IsInst τ) (θ : TypeSub) : s.IsInst (τ.subst θ) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨θ.comp σ, by rw [← Ty.subst_comp, hσ]⟩

theorem Ty.IsInst.refl (s : Ty) : s.IsInst s := ⟨Ty.var, Ty.subst_id s⟩

open Classical in
/-- The canonical instance substitution of an instance `τ` of `s`: the unique one on the type
variables of `s`, and a fixed type elsewhere. -/
noncomputable def Ty.constSub (s τ : Ty) (h : s.IsInst τ) : TypeSub :=
  fun i ↦ if i ∈ s.typeVars then (Classical.choose h) i else Ty.bool

theorem Ty.constSub_spec (s τ : Ty) (h : s.IsInst τ) : s.subst (Ty.constSub s τ h) = τ := by
  refine Eq.trans (Ty.subst_congr s (σ' := Classical.choose h) (fun i hi ↦ by simp [Ty.constSub, hi]))
    (Classical.choose_spec h)

theorem Ty.constSub_eq (s τ : Ty) (h : s.IsInst τ) {σ : TypeSub} (hσ : s.subst σ = τ) :
    ∀ i, i ∈ s.typeVars → Ty.constSub s τ h i = σ i := by
  intro i hi
  have := Ty.subst_unique s ((Classical.choose_spec h).trans hσ.symm) i hi
  simpa [Ty.constSub, hi] using this

theorem Ty.constSub_off (s τ : Ty) (h : s.IsInst τ) {i : Nat} (hi : i ∉ s.typeVars) :
    Ty.constSub s τ h i = Ty.bool := by
  simp [Ty.constSub, hi]

theorem Ty.constSub_inst (s τ : Ty) (h : s.IsInst τ) (θ : TypeSub) :
    ∀ i, i ∈ s.typeVars →
      Ty.constSub s (τ.subst θ) (h.inst θ) i = (Ty.constSub s τ h i).subst θ := by
  intro i hi
  have hs : s.subst (θ.comp (Ty.constSub s τ h)) = τ.subst θ := by
    rw [← Ty.subst_comp, Ty.constSub_spec]
  rw [Ty.constSub_eq s _ (h.inst θ) hs i hi]

end QEDFV.HOL
