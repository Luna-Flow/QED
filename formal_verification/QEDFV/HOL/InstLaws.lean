import QEDFV.HOL.TermLaws
import QEDFV.HOL.Instantiation

/-! Commutation of type instantiation with term substitution, and composition of type
instantiations on arbitrary contexts. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ Θ : List Ty} {a b : Ty}

/-- The substitution induced on type-instantiated contexts. -/
def Sub.mapTypes (θ : TypeSub) :
    {Γ Δ : List Ty} → Sub S Γ Δ → Sub S (Γ.map (Ty.subst θ)) (Δ.map (Ty.subst θ))
  | [], _, _ => fun v ↦ nomatch v
  | _ :: _, _, σ => fun v ↦
      match v with
      | .zero => (σ .zero).instType θ
      | .succ w => Sub.mapTypes θ (fun u ↦ σ (.succ u)) w

theorem Sub.mapTypes_apply (θ : TypeSub) (σ : Sub S Γ Δ) (v : Var Γ a) :
    Sub.mapTypes θ σ (v.mapTypes θ) = (σ v).instType θ := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (fun u ↦ σ (.succ u))

theorem Ren.mapTypes_id (θ : TypeSub) {c : Ty} (w : Var (Γ.map (Ty.subst θ)) c) :
    Ren.mapTypes θ (fun u ↦ u : Ren Γ Γ) w = w := by
  induction Γ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => rfl
      | succ w =>
          change Ren.mapTypes θ (fun u ↦ Var.succ u : Ren Γ (x :: Γ)) w = Var.succ w
          have := Ren.mapTypes_succ θ (fun u ↦ u : Ren Γ Γ) w (b := x)
          rw [this, ih]

theorem Ren.mapTypes_shift (θ : TypeSub) :
    @Eq (Ren (Γ.map (Ty.subst θ)) ((b :: Γ).map (Ty.subst θ)))
      (Ren.mapTypes θ (Var.succ : Ren Γ (b :: Γ))) (Var.succ) := by
  funext c w
  have := Ren.mapTypes_succ θ (fun u ↦ u : Ren Γ Γ) w (b := b)
  rw [Ren.mapTypes_id] at this
  exact this

theorem Sub.mapTypes_rename (θ : TypeSub) (σ : Sub S Γ Δ) (r : Ren Δ Θ) {c : Ty}
    (w : Var (Γ.map (Ty.subst θ)) c) :
    Sub.mapTypes θ (fun u ↦ (σ u).rename r) w
      = (Sub.mapTypes θ σ w).rename (Ren.mapTypes θ r) := by
  induction Γ generalizing Δ Θ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => exact Term.rename_instType (σ .zero) θ r
      | succ w => exact ih (fun u ↦ σ (.succ u)) r w

theorem Sub.mapTypes_lift (θ : TypeSub) (σ : Sub S Γ Δ) :
    @Eq (Sub S ((b :: Γ).map (Ty.subst θ)) ((b :: Δ).map (Ty.subst θ)))
      (Sub.mapTypes θ (Sub.lift σ : Sub S (b :: Γ) (b :: Δ)))
      (Sub.lift (Sub.mapTypes θ σ)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w =>
      change Sub.mapTypes θ (fun u ↦ (σ u).rename Var.succ) w
        = (Sub.mapTypes θ σ w).rename Var.succ
      rw [Sub.mapTypes_rename, Ren.mapTypes_shift]

theorem Term.substitute_cast {h : a = b} (t : Term S Γ a) (σ : Sub S Γ Δ) :
    (h ▸ t).substitute σ = h ▸ t.substitute σ := by
  cases h; rfl

theorem Term.substitute_instType (t : Term S Γ a) (σ : Sub S Γ Δ) (θ : TypeSub) :
    (t.substitute σ).instType θ = (t.instType θ).substitute (Sub.mapTypes θ σ) := by
  induction t generalizing Δ with
  | var v => exact (Sub.mapTypes_apply θ σ v).symm
  | const c τ => simp only [Term.substitute, Term.instType, Term.substitute_cast]
  | app f x ihf ihx => simp only [Term.substitute, Term.instType, ihf, ihx]
  | lam b ih => simp only [Term.substitute, Term.instType, ih, Sub.mapTypes_lift]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.substitute, Term.instType, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.substitute, Term.instType, ihp, ihq]
  | all p ih => simp only [Term.substitute, Term.instType, ih, Sub.mapTypes_lift]
  | ex p ih => simp only [Term.substitute, Term.instType, ih, Sub.mapTypes_lift]
  | eq => rfl
  | choice => rfl

/-! ### Composition of instantiations on arbitrary contexts -/

theorem ctx_map_comp (Γ : List Ty) (σ θ : TypeSub) :
    (Γ.map (Ty.subst σ)).map (Ty.subst θ) = Γ.map (Ty.subst (θ.comp σ)) := by
  induction Γ with
  | nil => rfl
  | cons x Γ ih => simp [List.map, Ty.subst_comp, ih]

theorem Term.instType_instType_heq (t : Term S Γ a) (σ θ : TypeSub) :
    HEq ((t.instType σ).instType θ) (t.instType (θ.comp σ)) :=
  Term.erase_inj_heq' _ _ (ctx_map_comp Γ σ θ) (Ty.subst_comp a θ σ) (by
    rw [Term.erase_instType, Term.erase_instType, Term.erase_instType, UTerm.inst_comp])

theorem typeSubstSequent_comp (s : Sequent S Γ) (σ θ : TypeSub) :
    HEq (typeSubstSequent θ (typeSubstSequent σ s)) (typeSubstSequent (θ.comp σ) s) := by
  have key : ∀ {Γ1 Γ2 : List Ty} (h : Γ1 = Γ2) (s1 : Sequent S Γ1) (s2 : Sequent S Γ2),
      s1.hyps.length = s2.hyps.length →
      (∀ i (h1 : i < s1.hyps.length) (h2 : i < s2.hyps.length),
        HEq (s1.hyps[i]) (s2.hyps[i])) → HEq s1.concl s2.concl → HEq s1 s2 := by
    intro Γ1 Γ2 h s1 s2 hl hh hc
    subst h
    cases s1 with
    | mk h1 c1 =>
      cases s2 with
      | mk h2 c2 =>
        have e1 : h1 = h2 := List.ext_getElem hl fun i a b ↦ eq_of_heq (hh i a b)
        have e2 : c1 = c2 := eq_of_heq hc
        subst e1; subst e2; rfl
  refine key (ctx_map_comp Γ σ θ) _ _ ?_ ?_ ?_
  · simp [typeSubstSequent]
  · intro i h1 h2
    simp only [typeSubstSequent, List.getElem_map]
    exact Term.instType_instType_heq _ σ θ
  · exact Term.instType_instType_heq _ σ θ

end QEDFV.HOL
