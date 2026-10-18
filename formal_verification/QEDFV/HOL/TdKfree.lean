import QEDFV.HOL.TdRules

/-! The translation is the identity on terms that avoid the defined constructor. -/
namespace QEDFV.HOL

/-- The instance substitutions of the constants of a term avoid the constructor `k`. -/
def Term.SigClean (k : Nat) : {Γ : List Ty} → {a : Ty} → Term S Γ a → Prop
  | _, _, .var _ => True
  | _, _, .const _ σ => ∀ i, k ∉ (σ i).tyCons
  | _, _, .app f x => Term.SigClean k f ∧ Term.SigClean k x
  | _, _, .lam b => Term.SigClean k b
  | _, _, .truth => True
  | _, _, .falsity => True
  | _, _, .conj p q => Term.SigClean k p ∧ Term.SigClean k q
  | _, _, .imp p q => Term.SigClean k p ∧ Term.SigClean k q
  | _, _, .all p => Term.SigClean k p
  | _, _, .ex p => Term.SigClean k p
  | _, _, .eq => True
  | _, _, .choice => True

theorem Var.erase_mapTy (f : Ty → Ty) {Γ : List Ty} {a : Ty} (v : Var Γ a) :
    (Var.mapTy f v).erase = v.erase := by
  induction v with
  | zero => rfl
  | succ v ih => simp [Var.mapTy, Var.erase, ih]

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

theorem nrmSub_kfree {Γ' : List Ty} {a : Ty} (h : G.k ∉ a.tyCons) :
    @Eq (Sub S (G.tr a :: Γ') (G.tr a :: Γ')) (G.nrmSub a Γ') (fun v ↦ Term.var v) := by
  funext c v
  cases v with
  | zero =>
      change G.nrmTy a (Term.var Var.zero) = Term.var Var.zero
      exact G.nrmTy_of_not_mem a h _
  | succ w => rfl

theorem substitute_id_erase {Γ : List Ty} {a : Ty} (t : Term S Γ a) :
    (t.substitute (fun v ↦ Term.var v)).erase = t.erase := by
  have := Term.substitute_var t (fun v ↦ v)
  rw [Term.rename_id] at this
  rw [this]

theorem tr_kfree {a : Ty} (h : G.k ∉ a.tyCons) : G.tr a = a := Ty.tr_of_not_mem a h

theorem erase_trans (hC : G.Closed) {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hk : G.k ∉ t.tyCons) (hs : t.SigClean G.k) : (G.trans hC t).erase = t.erase := by
  induction t with
  | var v => simp [trans, Term.erase, Var.erase_mapTy]
  | @const Γ c σ =>
      have hτ : G.k ∉ ((S c).subst σ).tyCons := hk
      have hc : G.k ∉ (S c).tyCons := by
        intro h; apply hτ; rw [Ty.tyCons_subst]; exact Or.inl h
      simp only [trans]
      rw [G.nrmTy_of_not_mem _ hτ]
      unfold rawConst
      rw [dif_pos hc, Term.erase_cast]
      simp only [Term.erase]
      congr 1
      funext i
      exact G.tr_kfree (hs i)
  | @app Γ a b f x ihf ihx =>
      have hf : G.k ∉ f.tyCons := fun h ↦ hk (Or.inl h)
      have hx : G.k ∉ x.tyCons := fun h ↦ hk (Or.inr h)
      have ha : G.k ∉ a.tyCons := fun h ↦
        hf (f.ty_tyCons_subset (by simp [Ty.tyCons]; exact Or.inl h))
      simp only [trans, Term.erase]
      rw [ihf hf hs.1, ihx hx hs.2, Ty.tr_of_not_mem a ha]
  | @lam a Γ b b0 ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hb : G.k ∉ b0.tyCons := fun h ↦ hk (Or.inr h)
      simp only [trans, Term.erase]
      rw [G.nrmSub_kfree ha, substitute_id_erase, ih hb hs, Ty.tr_of_not_mem a ha]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      simp only [trans, Term.erase, ihp hp hs.1, ihq hq hs.2]
  | imp p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      simp only [trans, Term.erase, ihp hp hs.1, ihq hq hs.2]
  | @all a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      simp only [trans, Term.erase]
      rw [G.nrmSub_kfree ha, substitute_id_erase, ih hp hs, G.tr_kfree ha]
  | @ex a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      simp only [trans, Term.erase]
      rw [G.nrmSub_kfree ha, substitute_id_erase, ih hp hs, G.tr_kfree ha]
  | @eq Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      simp only [trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, ha])]
      simp [Term.erase, G.tr_kfree ha]
  | @choice Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      simp only [trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, ha])]
      simp [Term.erase, G.tr_kfree ha]

end TypeDefGate

end QEDFV.HOL
