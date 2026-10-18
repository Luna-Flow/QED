import QEDFV.HOL.TdSubst

/-! Derived laws of the normalisation: substitution congruence, normalisation of an
application, and idempotence at every type. -/
namespace QEDFV.HOL

namespace HistoryDerivation

variable {S : Signature} {Γ : List Ty} {a b : Ty} {es : List (ModelExtension S)}

/-- Equal terms have equal substitution instances (Leibniz), via beta. -/
theorem leibniz {L : List (Term S Γ .bool)} {p : Term S (a :: Γ) b} {s t : Term S Γ a}
    (h : HistoryDerivation S es { hyps := L, concl := s.equal t }) :
    HistoryDerivation S es
      { hyps := L, concl := (p.substitute (Sub.single s)).equal (p.substitute (Sub.single t)) } := by
  have b1 : HistoryDerivation S es
      { hyps := L, concl := ((Term.lam p).app s).equal (p.substitute (Sub.single s)) } :=
    (HistoryDerivation.core (.beta p s)).mono (fun _ hh ↦ by simp at hh)
  have b2 : HistoryDerivation S es
      { hyps := L, concl := ((Term.lam p).app t).equal (p.substitute (Sub.single t)) } :=
    (HistoryDerivation.core (.beta p t)).mono (fun _ hh ↦ by simp at hh)
  exact trans' (sym b1) (trans' (mkComb' (refl' _) h) b2)

/-- Equalities transport along equalities of types. -/
theorem cast_equal {A B : Ty} (e : A = B) {L : List (Term S Γ .bool)} {x y : Term S Γ A}
    (h : HistoryDerivation S es { hyps := L, concl := x.equal y }) :
    HistoryDerivation S es { hyps := L, concl := (e ▸ x).equal (e ▸ y) } := by
  subst e; exact h

end HistoryDerivation

theorem Term.cast_cast {S : Signature} {Γ : List Ty} {A B : Ty} (e : A = B) (x : Term S Γ B) :
    (e ▸ (e.symm ▸ x : Term S Γ A) : Term S Γ B) = x := by
  subst e; rfl

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {Γ : List Ty} {es : List (ModelExtension S)}

/-- Normalisation is the identity at types that avoid the defined constructor. -/
theorem nrmTy_of_not_mem (N : G.Oracle) (τ : Ty) (h : G.k ∉ τ.tyCons) {Γ : List Ty} (u : Term S Γ (G.tr τ)) :
    G.nrmTy N τ u = u := by
  induction τ generalizing Γ with
  | bool => rfl
  | ind => rfl
  | var _ => rfl
  | arr a b iha ihb => simp only [nrmTy, if_neg h]
  | con j m args ih =>
      have hj : j ≠ G.k := fun e ↦ h (by simp [Ty.tyCons, e])
      have hh : ¬ (j = G.k ∧ m = G.n) := fun e ↦ hj e.1
      simp only [nrmTy, hh, if_false]

theorem nrmTy_arr_pos (N : G.Oracle) {a b : Ty} (hk : G.k ∈ (Ty.arr a b).tyCons) {Γ : List Ty}
    (u : Term S Γ (G.tr (.arr a b))) :
    G.nrmTy N (.arr a b) u
      = Term.lam (G.nrmTy N b ((u.rename Var.succ).app (G.nrmTy N a (Term.var Var.zero)))) := by
  simp only [nrmTy, if_pos hk]

/-- Normalisation respects derivable equality. -/
theorem nrmTy_congr (N : G.Oracle) (τ : Ty) {L : List (Term S Γ .bool)} {s t : Term S Γ (G.tr τ)}
    (h : HistoryDerivation S es { hyps := L, concl := s.equal t }) :
    HistoryDerivation S es { hyps := L, concl := (G.nrmTy N τ s).equal (G.nrmTy N τ t) } := by
  have := HistoryDerivation.leibniz
    (p := G.nrmTy N τ (Term.var Var.zero : Term S (G.tr τ :: Γ) (G.tr τ))) h
  rwa [G.nrmTy_substitute N, G.nrmTy_substitute N] at this

/-- Applying a normalised function: `norm_{a→b} u w = norm_b (u (norm_a w))`. -/
theorem nrm_app (N : G.Oracle) (a b : Ty) {L : List (Term S Γ .bool)} (u : Term S Γ (G.tr (.arr a b)))
    (w : Term S Γ (G.tr a)) :
    HistoryDerivation S es
      { hyps := L,
        concl := ((G.nrmTy N (.arr a b) u).app w).equal (G.nrmTy N b (u.app (G.nrmTy N a w))) } := by
  by_cases hk : G.k ∈ (Ty.arr a b).tyCons
  · simp only [nrmTy, if_pos hk]
    have hX : (G.nrmTy N b ((u.rename Var.succ).app (G.nrmTy N a (Term.var Var.zero)))).substitute
        (Sub.single w) = G.nrmTy N b (u.app (G.nrmTy N a w)) := by
      rw [G.nrmTy_substitute N]
      simp only [Term.substitute, G.nrmTy_substitute N, NormCfg.rename_succ_substitute_single]
      rfl
    have b1 := (HistoryDerivation.core (es := es)
      (Derivation.beta (G.nrmTy N b ((u.rename Var.succ).app (G.nrmTy N a (Term.var Var.zero)))) w)).mono
      (L := L) (fun _ hh ↦ by simp at hh)
    rw [hX] at b1
    exact b1
  · simp only [Ty.tyCons, Set.mem_union, not_or] at hk
    rw [G.nrmTy_of_not_mem N (.arr a b) (by simp [Ty.tyCons, hk.1, hk.2]),
      G.nrmTy_of_not_mem N a hk.1, G.nrmTy_of_not_mem N b hk.2]
    exact HistoryDerivation.refl' _

/-- The oracle is idempotent at every type. -/
def Idem (N : G.Oracle) (es : List (ModelExtension S)) : Prop :=
  ∀ (τ : Ty) {Γ : List Ty} (L : List (Term S Γ .bool)) (u : Term S Γ (G.tr τ)),
    HistoryDerivation S es
      { hyps := L, concl := (((N τ).closedLift).app (((N τ).closedLift).app u)).equal (((N τ).closedLift).app u) }

theorem nrmTy_idem (N : G.Oracle) (hI : G.Idem N es) (τ : Ty)
    {Γ : List Ty} (L : List (Term S Γ .bool)) (u : Term S Γ (G.tr τ)) :
    HistoryDerivation S es
      { hyps := L, concl := (G.nrmTy N τ (G.nrmTy N τ u)).equal (G.nrmTy N τ u) } := by
  induction τ generalizing Γ with
  | bool => exact HistoryDerivation.refl' _
  | ind => exact HistoryDerivation.refl' _
  | var _ => exact HistoryDerivation.refl' _
  | con j m args ih =>
      by_cases h : j = G.k ∧ m = G.n
      · simp only [nrmTy, h, and_self, if_true]
        exact hI _ L u
      · simp only [nrmTy, h, if_false]
        exact HistoryDerivation.refl' _
  | arr a b iha ihb =>
      by_cases hk : G.k ∈ (Ty.arr a b).tyCons
      · set W := G.nrmTy N (.arr a b) u with hW
        have e1 := G.nrmTy_arr_pos N hk W
        have e2 := G.nrmTy_arr_pos N hk u
        rw [← hW] at e2
        rw [e1]
        refine Eq.mpr (congrArg (fun t ↦ HistoryDerivation S es { hyps := L, concl := (Term.lam (G.nrmTy N b ((W.rename Var.succ).app (G.nrmTy N a (Term.var Var.zero))))).equal t }) e2) ?_
        refine HistoryDerivation.abs (A := { hyps := L, concl := Term.truth }) ?_
        set L' := (weakenSequent (b := G.tr a) ({ hyps := L, concl := Term.truth } :
          Sequent S Γ)).hyps with hL'
        set x : Term S (G.tr a :: Γ) (G.tr a) := Term.var Var.zero with hx
        have hWr : (W.rename Var.succ : Term S (G.tr a :: Γ) (G.tr (.arr a b))) = G.nrmTy N (.arr a b) (u.rename Var.succ) := by
          rw [hW, G.nrmTy_rename N]
        rw [hWr]
        have s1 := G.nrm_app N a b (L := L') (u.rename Var.succ) (G.nrmTy N a x) (es := es)
        have s2 := G.nrmTy_congr N b s1
        have s3 := ihb L' (((u.rename Var.succ).app (G.nrmTy N a (G.nrmTy N a x))))
        have s4 : HistoryDerivation S es { hyps := L', concl := (G.nrmTy N b ((u.rename Var.succ).app (G.nrmTy N a (G.nrmTy N a x)))).equal (G.nrmTy N b ((u.rename Var.succ).app (G.nrmTy N a x))) } :=
          G.nrmTy_congr N b (HistoryDerivation.mkComb' (HistoryDerivation.refl' _) (iha L' x))
        exact HistoryDerivation.trans' s2 (HistoryDerivation.trans' s3 s4)
      · simp only [nrmTy, if_neg hk]
        exact HistoryDerivation.refl' _

end TypeDefGate

end QEDFV.HOL
