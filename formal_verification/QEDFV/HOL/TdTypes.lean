import QEDFV.HOL.InstLaws

/-! Type translation for the erasure of a type definition whose representation type is
closed: every occurrence of the defined constructor `k(args)` is replaced by the
representation type. -/
namespace QEDFV.HOL

/-- Replace the constructor `k` of arity `n` by the (closed) representation type `R`. -/
def Ty.tr : Ty → Nat → Nat → Ty → Ty
  | .bool, _, _, _ => .bool
  | .ind, _, _, _ => .ind
  | .var i, _, _, _ => .var i
  | .arr a b, k, n, R => .arr (a.tr k n R) (b.tr k n R)
  | .con j m args, k, n, R =>
      if j = k ∧ m = n then R else .con j m (fun i ↦ (args i).tr k n R)

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

theorem Ty.tr_subst (hR : ∀ i, i ∉ R.typeVars) (a : Ty) (σ : TypeSub) :
    (a.subst σ).tr k n R = (a.tr k n R).subst (fun i ↦ (σ i).tr k n R) := by
  induction a with
  | bool => rfl
  | ind => rfl
  | var i => rfl
  | arr a b iha ihb => simp only [Ty.subst, Ty.tr, iha, ihb]
  | con j m args ih =>
      by_cases h : j = k ∧ m = n
      · simp [Ty.subst, Ty.tr, h, Ty.subst_of_closed R hR]
      · simp only [Ty.subst, Ty.tr, h, if_false]
        congr 1
        funext i
        exact ih i

end

end QEDFV.HOL
