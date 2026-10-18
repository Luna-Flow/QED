import QEDFV.HOL.InstLaws

/-! Type translation for the erasure of a type definition whose representation type is
closed: every occurrence of the defined constructor `k(args)` is replaced by the
representation type. -/
namespace QEDFV.HOL

/-- The substitution that sends the first `m` type variables to the given types and leaves the
others fixed. -/
def Ty.argsSub (m : Nat) (f : Fin m → Ty) : TypeSub :=
  fun i ↦ if h : i < m then f ⟨i, h⟩ else Ty.var i

/-- Replace the constructor `k` of arity `n` by the representation type `R`, whose type
variables `0..n-1` stand for the arguments. -/
def Ty.tr : Ty → Nat → Nat → Ty → Ty
  | .bool, _, _, _ => .bool
  | .ind, _, _, _ => .ind
  | .var i, _, _, _ => .var i
  | .arr a b, k, n, R => .arr (a.tr k n R) (b.tr k n R)
  | .con j m args, k, n, R =>
      if j = k ∧ m = n then R.subst (Ty.argsSub m (fun i ↦ (args i).tr k n R))
      else .con j m (fun i ↦ (args i).tr k n R)

section
variable {k n : Nat} {R : Ty}

theorem Ty.tr_of_not_mem (a : Ty) (h : k ∉ a.tyCons) : a.tr k n R = a := by
  induction a with
  | bool => rfl
  | ind => rfl
  | var i => rfl
  | arr a b iha ihb =>
      simp only [Ty.tyCons, Set.mem_union, not_or] at h
      simp only [Ty.tr, iha h.1, ihb h.2]
  | con j m args ih =>
      have hj : j ≠ k := fun e ↦ h (by simp [Ty.tyCons, e])
      simp only [Ty.tr, hj, false_and, if_false]
      congr 1
      funext i
      exact ih i (fun hi ↦ h (by simp only [Ty.tyCons]; exact Or.inr ⟨i, hi⟩))

theorem Ty.subst_of_closed (R : Ty) (hR : ∀ i, i ∉ R.typeVars) (θ : TypeSub) :
    R.subst θ = R := by
  induction R with
  | bool => rfl
  | ind => rfl
  | var i => exact absurd (by simp [Ty.typeVars]) (hR i)
  | arr a b iha ihb =>
      simp only [Ty.typeVars, Set.mem_union, not_or] at hR
      simp only [Ty.subst, iha (fun i hi ↦ (hR i).1 hi), ihb (fun i hi ↦ (hR i).2 hi)]
  | con j m args ih =>
      simp only [Ty.subst]
      congr 1
      funext i
      exact ih i (fun i' hi ↦ hR i' (by simp only [Ty.typeVars]; exact ⟨i, hi⟩))

theorem Ty.tr_subst (hR : ∀ i, i ∈ R.typeVars → i < n) (a : Ty) (σ : TypeSub) :
    (a.subst σ).tr k n R = (a.tr k n R).subst (fun i ↦ (σ i).tr k n R) := by
  induction a with
  | bool => rfl
  | ind => rfl
  | var i => rfl
  | arr a b iha ihb => simp only [Ty.subst, Ty.tr, iha, ihb]
  | con j m args ih =>
      by_cases h : j = k ∧ m = n
      · simp only [Ty.subst, Ty.tr, h, and_self, if_true]
        rw [Ty.subst_comp]
        refine Ty.subst_congr R (fun i hi ↦ ?_)
        have hi' : i < m := h.2 ▸ hR i hi
        simp only [Ty.argsSub, hi', dite_true, TypeSub.comp]
        exact ih ⟨i, hi'⟩
      · simp only [Ty.subst, Ty.tr, h, if_false]
        congr 1
        funext i
        exact ih i

end

end QEDFV.HOL
