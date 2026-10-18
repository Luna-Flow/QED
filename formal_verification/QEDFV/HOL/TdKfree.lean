import QEDFV.HOL.TdRules

/-! The translation is the identity on terms that avoid the defined constructor. -/
namespace QEDFV.HOL

/-- The instance substitutions of the constants of a term avoid the constructor `k`. -/
def Term.SigClean (k : Nat) : {Γ : List Ty} → {a : Ty} → Term S Γ a → Prop
  | _, _, .var _ => True
  | _, _, .const c σ => ∀ i, k ∉ (σ i).tyCons ∧ (i ∉ (S c).typeVars → σ i = Ty.var i)
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
      by_cases hi : i ∈ (S c).typeVars
      · simp [canonSub, hi, G.tr_kfree (hs i).1]
      · simp [canonSub, hi, (hs i).2 hi]
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

namespace QEDFV.HOL

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- Ground terms: no type variable occurs in any type annotation. -/
def Term.Ground {Γ : List Ty} {a : Ty} (t : Term S Γ a) : Prop := t.annotVars = ∅

theorem tr_ground (hC : G.Closed) {a : Ty} (h : G.k ∉ a.tyCons) (hv : a.typeVars = ∅)
    (θ : TypeSub) : G.tr (a.subst θ) = a := by
  have : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hv] at hi; exact hi) θ
  rw [this]; exact G.tr_kfree h

theorem trans_cast (hC : G.Closed) {Γ : List Ty} {a b : Ty} (h : a = b) (t : Term S Γ a) :
    G.trans hC (h ▸ t) = (congrArg G.tr h) ▸ G.trans hC t := by
  subst h; rfl

/-- Translating the identity instance of a clean term is translating the term. -/
theorem erase_trans_var (hC : G.Closed) {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hk : G.k ∉ t.tyCons) (hs : t.SigClean G.k) :
    (G.trans hC (t.instType Ty.var)).erase = t.erase := by
  induction t with
  | var v => simp [Term.instType, trans, Term.erase, Var.erase_mapTy, Var.erase_mapTypes]
  | @const Γ c σ =>
      have hτ : G.k ∉ ((S c).subst σ).tyCons := hk
      have hc : G.k ∉ (S c).tyCons := by
        intro h; apply hτ; rw [Ty.tyCons_subst]; exact Or.inl h
      have hτ' : (S c).subst (TypeSub.comp Ty.var σ) = (S c).subst σ := by
        rw [← Ty.subst_comp, Ty.subst_id]
      simp only [Term.instType]
      rw [G.trans_cast hC, Term.erase_cast]
      simp only [trans]
      rw [G.nrmTy_of_not_mem _ (by rw [hτ']; exact hτ)]
      unfold rawConst
      rw [dif_pos hc, Term.erase_cast]
      simp only [Term.erase]
      congr 1
      funext i
      by_cases hi : i ∈ (S c).typeVars
      · simp only [canonSub, hi, if_true, TypeSub.comp, Ty.subst_id]
        exact G.tr_kfree (hs i).1
      · simp [canonSub, hi, (hs i).2 hi]
  | @app Γ a b f x ihf ihx =>
      have hf : G.k ∉ f.tyCons := fun h ↦ hk (Or.inl h)
      have hx : G.k ∉ x.tyCons := fun h ↦ hk (Or.inr h)
      have ha : G.k ∉ a.tyCons := fun h ↦
        hf (f.ty_tyCons_subset (by simp [Ty.tyCons]; exact Or.inl h))
      have htg : (a.subst Ty.var).tr G.k G.n G.repTy = a := by
        rw [Ty.subst_id]; exact G.tr_kfree ha
      simp only [Term.instType, trans, Term.erase]
      rw [ihf hf hs.1, ihx hx hs.2, htg]
  | @lam a Γ b b0 ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hb : G.k ∉ b0.tyCons := fun h ↦ hk (Or.inr h)
      have hsub : a.subst Ty.var = a := Ty.subst_id a
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hb hs, hsub]
      first | rw [G.tr_kfree ha] | rw [Ty.tr_of_not_mem a ha]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      simp only [Term.instType, trans, Term.erase, ihp hp hs.1, ihq hq hs.2]
  | imp p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      simp only [Term.instType, trans, Term.erase, ihp hp hs.1, ihq hq hs.2]
  | @all a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      have hsub : a.subst Ty.var = a := Ty.subst_id a
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hp hs, hsub]
      first | rw [G.tr_kfree ha] | rw [Ty.tr_of_not_mem a ha]
  | @ex a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      have hsub : a.subst Ty.var = a := Ty.subst_id a
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hp hs, hsub]
      first | rw [G.tr_kfree ha] | rw [Ty.tr_of_not_mem a ha]
  | @eq Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      have hsub : a.subst Ty.var = a := Ty.subst_id a
      simp only [Term.instType, trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, hsub, ha])]
      simp [Term.erase, hsub, G.tr_kfree ha]
  | @choice Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      have hsub : a.subst Ty.var = a := Ty.subst_id a
      simp only [Term.instType, trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, hsub, ha])]
      simp [Term.erase, hsub, G.tr_kfree ha]

/-- Translating an instance of a ground clean term is the same as translating the term. -/
theorem erase_trans_inst (hC : G.Closed) {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hk : G.k ∉ t.tyCons) (hs : t.SigClean G.k) (hg : t.annotVars = ∅) (θ : TypeSub) :
    (G.trans hC (t.instType θ)).erase = t.erase := by
  induction t with
  | var v => simp [Term.instType, trans, Term.erase, Var.erase_mapTy, Var.erase_mapTypes]
  | @const Γ c σ =>
      have hτ : G.k ∉ ((S c).subst σ).tyCons := hk
      have hτv : ((S c).subst σ).typeVars = ∅ := hg
      have hc : G.k ∉ (S c).tyCons := by
        intro h; apply hτ; rw [Ty.tyCons_subst]; exact Or.inl h
      have hτ' : (S c).subst (θ.comp σ) = (S c).subst σ := by
        rw [← Ty.subst_comp]
        exact Ty.subst_of_closed _ (fun i hi ↦ by rw [hτv] at hi; exact hi) θ
      simp only [Term.instType]
      rw [G.trans_cast hC, Term.erase_cast]
      simp only [trans]
      rw [G.nrmTy_of_not_mem _ (by rw [hτ']; exact hτ)]
      unfold rawConst
      rw [dif_pos hc, Term.erase_cast]
      simp only [Term.erase]
      congr 1
      funext i
      by_cases hi : i ∈ (S c).typeVars
      · have hcl : (σ i).typeVars = ∅ := by
          ext j; constructor
          · intro hj
            have : j ∈ ((S c).subst σ).typeVars := by
              rw [Ty.typeVars_subst]; exact ⟨i, hi, hj⟩
            rw [hτv] at this; exact this
          · intro hj; exact absurd hj (by simp)
        have hsub : (σ i).subst θ = σ i :=
          Ty.subst_of_closed _ (fun j hj ↦ by rw [hcl] at hj; exact hj) θ
        simp only [canonSub, hi, if_true, TypeSub.comp, hsub]
        exact G.tr_kfree (hs i).1
      · simp [canonSub, hi, (hs i).2 hi]
  | @app Γ a b f x ihf ihx =>
      have hf : G.k ∉ f.tyCons := fun h ↦ hk (Or.inl h)
      have hx : G.k ∉ x.tyCons := fun h ↦ hk (Or.inr h)
      have hgf : f.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hgx : x.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      have ha : G.k ∉ a.tyCons := fun h ↦
        hf (f.ty_tyCons_subset (by simp [Ty.tyCons]; exact Or.inl h))
      have hav : a.typeVars = ∅ := by
        have := f.ty_annotVars_subset
        rw [hgf] at this
        ext i; constructor
        · intro hi; exact (this (by simp [Ty.typeVars]; exact Or.inl hi) : i ∈ (∅ : Set Nat))
        · intro hi; exact absurd hi (by simp)
      simp only [Term.instType, trans, Term.erase]
      have htg := G.tr_ground hC ha hav θ
      simp only [tr] at htg
      rw [ihf hf hs.1 hgf, ihx hx hs.2 hgx, htg]
  | @lam a Γ b b0 ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hb : G.k ∉ b0.tyCons := fun h ↦ hk (Or.inr h)
      have hav : a.typeVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hbv : b0.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      have hsub : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hav] at hi; exact hi) θ
      have htg := G.tr_ground hC ha hav θ
      simp only [tr] at htg
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hb hs hbv, htg]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      have hgp : p.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hgq : q.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      simp only [Term.instType, trans, Term.erase, ihp hp hs.1 hgp, ihq hq hs.2 hgq]
  | imp p q ihp ihq =>
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inl h)
      have hq : G.k ∉ q.tyCons := fun h ↦ hk (Or.inr h)
      have hgp : p.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hgq : q.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      simp only [Term.instType, trans, Term.erase, ihp hp hs.1 hgp, ihq hq hs.2 hgq]
  | @all a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      have hav : a.typeVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hpv : p.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      have hsub : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hav] at hi; exact hi) θ
      have htg := G.tr_ground hC ha hav θ
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hp hs hpv, htg]
  | @ex a Γ p ih =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (Or.inl h)
      have hp : G.k ∉ p.tyCons := fun h ↦ hk (Or.inr h)
      have hav : a.typeVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.1
      have hpv : p.annotVars = ∅ := by
        have := hg; simp only [Term.annotVars, Set.union_empty_iff] at this; exact this.2
      have hsub : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hav] at hi; exact hi) θ
      have htg := G.tr_ground hC ha hav θ
      simp only [Term.instType, trans, Term.erase]
      rw [G.nrmSub_kfree (by rw [hsub]; exact ha), substitute_id_erase, ih hp hs hpv, htg]
  | @eq Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      have hav : a.typeVars = ∅ := by
        have : (Ty.arr a (Ty.arr a Ty.bool)).typeVars = ∅ := hg
        simp only [Ty.typeVars, Set.union_empty_iff] at this
        exact this.1
      have hsub : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hav] at hi; exact hi) θ
      have htg := G.tr_ground hC ha hav θ
      simp only [Term.instType, trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, hsub, ha])]
      simp [Term.erase, htg]
  | @choice Γ a =>
      have ha : G.k ∉ a.tyCons := fun h ↦ hk (by simp [Term.tyCons, Ty.tyCons, h])
      have hav : a.typeVars = ∅ := by
        have : (Ty.arr (Ty.arr a Ty.bool) a).typeVars = ∅ := hg
        simp only [Ty.typeVars, Set.union_empty_iff] at this
        exact this.2
      have hsub : a.subst θ = a := Ty.subst_of_closed a (fun i hi ↦ by rw [hav] at hi; exact hi) θ
      have htg := G.tr_ground hC ha hav θ
      simp only [Term.instType, trans]
      rw [G.nrmTy_of_not_mem _ (by simp [Ty.tyCons, hsub, ha])]
      simp [Term.erase, htg]

end TypeDefGate

end QEDFV.HOL
