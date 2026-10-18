import QEDFV.HOL.TdTerms

/-! Commutation of the normalisation and the term translation with renaming and
substitution. -/
namespace QEDFV.HOL

/-! ### The renaming and substitution induced by a type map -/

/-- The renaming induced on contexts mapped by a type function. -/
def Ren.mapTy (f : Ty → Ty) :
    {Γ Δ : List Ty} → Ren Γ Δ → Ren (Γ.map f) (Δ.map f)
  | [], _, _ => fun v ↦ nomatch v
  | _ :: _, _, r => fun v ↦
      match v with
      | .zero => Var.mapTy f (r .zero)
      | .succ w => Ren.mapTy f (fun u ↦ r (.succ u)) w

theorem Ren.mapTy_apply (f : Ty → Ty) (r : Ren Γ Δ) (v : Var Γ a) :
    Ren.mapTy f r (Var.mapTy f v) = Var.mapTy f (r v) := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (fun u ↦ r (.succ u))

theorem Ren.mapTy_succ (f : Ty → Ty) (r : Ren Γ Δ) {c : Ty} {b : Ty}
    (w : Var (Γ.map f) c) :
    Ren.mapTy f (fun u ↦ Var.succ (r u) : Ren Γ (b :: Δ)) w
      = Var.succ (Ren.mapTy f r w) := by
  induction Γ generalizing Δ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => rfl
      | succ w => exact ih (fun u ↦ r (.succ u)) w

theorem Ren.mapTy_id (f : Ty → Ty) {c : Ty} (w : Var (Γ.map f) c) :
    Ren.mapTy f (fun u ↦ u : Ren Γ Γ) w = w := by
  induction Γ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => rfl
      | succ w =>
          change Ren.mapTy f (fun u ↦ Var.succ u : Ren Γ (x :: Γ)) w = Var.succ w
          have := Ren.mapTy_succ f (fun u ↦ u : Ren Γ Γ) w (b := x)
          rw [this, ih]

theorem Ren.mapTy_lift (f : Ty → Ty) (r : Ren Γ Δ) {b : Ty} :
    @Eq (Ren ((b :: Γ).map f) ((b :: Δ).map f))
      (Ren.mapTy f (Ren.lift r : Ren (b :: Γ) (b :: Δ)))
      (Ren.lift (Ren.mapTy f r)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w => exact Ren.mapTy_succ f r w

theorem Ren.mapTy_shift (f : Ty → Ty) {b : Ty} :
    @Eq (Ren (Γ.map f) ((b :: Γ).map f))
      (Ren.mapTy f (Var.succ : Ren Γ (b :: Γ))) (Var.succ) := by
  funext c w
  have := Ren.mapTy_succ f (fun u ↦ u : Ren Γ Γ) w (b := b)
  rw [Ren.mapTy_id] at this
  exact this


theorem Sub.comp_lift (ρ1 : Sub S Γ Δ) (ρ2 : Sub S Δ Θ) {b : Ty} :
    @Eq (Sub S (b :: Γ) (b :: Θ))
      (fun {_} v ↦ ((Sub.lift ρ1) v).substitute (Sub.lift ρ2))
      (Sub.lift (fun {_} v ↦ (ρ1 v).substitute ρ2)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w =>
      change ((ρ1 w).rename Var.succ).substitute (Sub.lift ρ2)
        = ((ρ1 w).substitute ρ2).rename Var.succ
      rw [Term.substitute_rename, Term.rename_substitute]
      rfl

theorem Term.substitute_substitute {S : Signature} {Γ Δ Θ : List Ty} {a : Ty}
    (t : Term S Γ a) (ρ1 : Sub S Γ Δ) (ρ2 : Sub S Δ Θ) :
    (t.substitute ρ1).substitute ρ2 = t.substitute (fun {_} v ↦ (ρ1 v).substitute ρ2) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | const c σ => rfl
  | app f x ihf ihx => simp only [Term.substitute, ihf, ihx]
  | lam b ih => simp only [Term.substitute, ih, Sub.comp_lift]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.substitute, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.substitute, ihp, ihq]
  | all p ih => simp only [Term.substitute, ih, Sub.comp_lift]
  | ex p ih => simp only [Term.substitute, ih, Sub.comp_lift]
  | eq => rfl
  | choice => rfl

/-- The substitution induced on contexts mapped by the type translation. -/
noncomputable def Sub.transS {S : Signature} (G : TypeDefGate S) (hC : G.Closed) :
    {Γ Δ : List Ty} → Sub S Γ Δ → Sub S (Γ.map G.tr) (Δ.map G.tr)
  | [], _, _ => fun v ↦ nomatch v
  | _ :: _, _, σ => fun v ↦
      match v with
      | .zero => G.trans hC (σ .zero)
      | .succ w => Sub.transS G hC (fun u ↦ σ (.succ u)) w

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {Γ Δ Θ : List Ty}

theorem predIn_rename (r : Ren Γ Δ) : (G.predIn Γ).rename r = G.predIn Δ := by
  rw [predIn_eq, predIn_eq]
  exact Term.closedLift_rename _ _

theorem normBody_rename (t : Term S Γ G.repTy) (r : Ren Γ Δ) :
    (G.normBody t).rename (Ren.lift r) = G.normBody (t.rename r) := by
  have h1 : ((t.rename Var.succ).rename (Ren.lift r) : Term S (G.repTy :: Δ) G.repTy)
      = (t.rename r).rename Var.succ := by
    rw [Term.rename_rename, Term.rename_rename]
    rfl
  simp only [normBody, holds', Term.rename, predIn_rename, h1]
  rfl

theorem normSel_rename (t : Term S Γ G.repTy) (r : Ren Γ Δ) :
    (G.normSel t).rename r = G.normSel (t.rename r) := by
  simp only [normSel, Term.rename, normBody_rename]

theorem nrm_rename (t : Term S Γ G.repTy) (r : Ren Γ Δ) :
    (G.nrm t).rename r = G.nrm (t.rename r) := by
  simp only [nrm, normIn, Term.rename, normSel_rename]
  rfl

theorem nrm_substitute (t : Term S Γ G.repTy) (σ : Sub S Γ Δ) :
    (G.nrm t).substitute σ = G.nrm (t.substitute σ) := by
  simp only [nrm, normIn, Term.substitute, normSel_substitute]
  rfl

theorem nrmTy_rename (τ : Ty) {Γ Δ : List Ty} (u : Term S Γ (G.tr τ)) (r : Ren Γ Δ) :
    (G.nrmTy τ u).rename r = G.nrmTy τ (u.rename r) := by
  induction τ generalizing Γ Δ with
  | bool => rfl
  | ind => rfl
  | var _ => rfl
  | arr a b iha ihb =>
      by_cases hk : G.k ∈ (Ty.arr a b).tyCons
      swap
      · simp only [nrmTy, if_neg hk]
      simp only [nrmTy, if_pos hk, Term.rename]
      rw [ihb]
      have e1 : ((u.rename Var.succ).rename (Ren.lift r) : Term S (G.tr a :: Δ) (G.tr (.arr a b)))
          = (u.rename r).rename Var.succ := by
        rw [Term.rename_rename, Term.rename_rename]; rfl
      have e2 : (G.nrmTy a (Term.var Var.zero : Term S (G.tr a :: Γ) (G.tr a))).rename (Ren.lift r)
          = G.nrmTy a (Term.var Var.zero) := by
        rw [iha]; rfl
      simp only [Term.rename, e1, e2]
  | con j m args ih =>
      by_cases h : j = G.k ∧ m = G.n
      · simp only [nrmTy, h, and_self, dite_true, Term.rename_cast, nrm_rename]
      · simp only [nrmTy, h, dite_false]

theorem nrmTy_substitute (τ : Ty) {Γ Δ : List Ty} (u : Term S Γ (G.tr τ)) (σ : Sub S Γ Δ) :
    (G.nrmTy τ u).substitute σ = G.nrmTy τ (u.substitute σ) := by
  induction τ generalizing Γ Δ with
  | bool => rfl
  | ind => rfl
  | var _ => rfl
  | arr a b iha ihb =>
      by_cases hk : G.k ∈ (Ty.arr a b).tyCons
      swap
      · simp only [nrmTy, if_neg hk]
      simp only [nrmTy, if_pos hk, Term.substitute]
      rw [ihb]
      have e1 : ((u.rename Var.succ).substitute (Sub.lift σ) : Term S (G.tr a :: Δ) (G.tr (.arr a b)))
          = (u.substitute σ).rename Var.succ := by
        rw [Term.substitute_rename, Term.rename_substitute]; rfl
      have e2 : (G.nrmTy a (Term.var Var.zero : Term S (G.tr a :: Γ) (G.tr a))).substitute (Sub.lift σ)
          = G.nrmTy a (Term.var Var.zero) := by
        rw [iha]; rfl
      simp only [Term.substitute, e1, e2]
  | con j m args ih =>
      by_cases h : j = G.k ∧ m = G.n
      · simp only [nrmTy, h, and_self, dite_true, Term.substitute_cast, nrm_substitute]
      · simp only [nrmTy, h, dite_false]

theorem rawConst_rename (hC : G.Closed) (c : Nat) (τ : Ty) (hτ : (S c).IsInst τ) {Δ Θ : List Ty} (r : Ren Δ Θ) :
    (G.rawConst hC c τ hτ : Term S Δ _).rename r = G.rawConst hC c τ hτ := by
  unfold rawConst
  by_cases h1 : G.k ∉ (S c).tyCons
  · rw [dif_pos h1, dif_pos h1]; rfl
  · by_cases h2 : c = G.rep
    · rw [dif_neg h1, dif_neg h1, dif_pos h2, dif_pos h2, Term.rename_cast]; rfl
    · by_cases h3 : c = G.abs
      · rw [dif_neg h1, dif_neg h1, dif_neg h2, dif_neg h2, dif_pos h3, dif_pos h3,
          Term.rename_cast]; rfl
      · rw [dif_neg h1, dif_neg h1, dif_neg h2, dif_neg h2, dif_neg h3, dif_neg h3]; rfl

theorem rawConst_substitute (hC : G.Closed) (c : Nat) (τ : Ty) (hτ : (S c).IsInst τ) {Δ Θ : List Ty}
    (ρ : Sub S Δ Θ) :
    (G.rawConst hC c τ hτ : Term S Δ _).substitute ρ = G.rawConst hC c τ hτ := by
  unfold rawConst
  by_cases h1 : G.k ∉ (S c).tyCons
  · rw [dif_pos h1, dif_pos h1]; rfl
  · by_cases h2 : c = G.rep
    · rw [dif_neg h1, dif_neg h1, dif_pos h2, dif_pos h2, Term.substitute_cast]; rfl
    · by_cases h3 : c = G.abs
      · rw [dif_neg h1, dif_neg h1, dif_neg h2, dif_neg h2, dif_pos h3, dif_pos h3,
          Term.substitute_cast]; rfl
      · rw [dif_neg h1, dif_neg h1, dif_neg h2, dif_neg h2, dif_neg h3, dif_neg h3]; rfl

theorem nrmSub_rename (a : Ty) (r : Ren Γ Δ) :
    @Eq (Sub S (G.tr a :: Γ) (G.tr a :: Δ))
      (fun {_} v ↦ (G.nrmSub a Γ v).rename (Ren.lift r))
      (fun {_} v ↦ G.nrmSub a Δ (Ren.lift r v)) := by
  funext c v
  cases v with
  | zero =>
      change (G.nrmTy a (Term.var Var.zero)).rename (Ren.lift r) = G.nrmTy a (Term.var Var.zero)
      rw [G.nrmTy_rename]; rfl
  | succ w => rfl

theorem trans_rename (hC : G.Closed) {a : Ty} (t : Term S Γ a) (r : Ren Γ Δ) :
    (G.trans hC t).rename (Ren.mapTy G.tr r) = G.trans hC (t.rename r) := by
  induction t generalizing Δ with
  | var v => exact congrArg Term.var (Ren.mapTy_apply G.tr r v)
  | const c τ hτ =>
      simp only [trans, Term.rename]
      rw [G.nrmTy_rename, G.rawConst_rename]
  | app f x ihf ihx => simp only [trans, Term.rename, ihf, ihx]
  | lam b ih =>
      simp only [trans, Term.rename]
      rw [Term.rename_substitute, ← ih, Ren.mapTy_lift, Term.substitute_rename]
      congr 2
      exact G.nrmSub_rename _ _
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [trans, Term.rename, ihp, ihq]
  | imp p q ihp ihq => simp only [trans, Term.rename, ihp, ihq]
  | all p ih =>
      simp only [trans, Term.rename]
      rw [Term.rename_substitute, ← ih, Ren.mapTy_lift, Term.substitute_rename]
      congr 2
      exact G.nrmSub_rename _ _
  | ex p ih =>
      simp only [trans, Term.rename]
      rw [Term.rename_substitute, ← ih, Ren.mapTy_lift, Term.substitute_rename]
      congr 2
      exact G.nrmSub_rename _ _
  | eq =>
      simp only [trans]
      rw [G.nrmTy_rename]; rfl
  | choice =>
      simp only [trans]
      rw [G.nrmTy_rename]; rfl

theorem transS_apply (hC : G.Closed) (σ : Sub S Γ Δ) {a : Ty} (v : Var Γ a) :
    Sub.transS G hC σ (Var.mapTy G.tr v) = G.trans hC (σ v) := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (fun u ↦ σ (.succ u))

theorem transS_rename (hC : G.Closed) (σ : Sub S Γ Δ) (r : Ren Δ Θ) {c : Ty}
    (w : Var (Γ.map G.tr) c) :
    Sub.transS G hC (fun {_} u ↦ (σ u).rename r) w
      = (Sub.transS G hC σ w).rename (Ren.mapTy G.tr r) := by
  induction Γ generalizing Δ Θ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => exact (G.trans_rename hC (σ .zero) r).symm
      | succ w => exact ih (fun u ↦ σ (.succ u)) r w

theorem transS_lift (hC : G.Closed) (σ : Sub S Γ Δ) {b : Ty} :
    @Eq (Sub S ((b :: Γ).map G.tr) ((b :: Δ).map G.tr))
      (Sub.transS G hC (Sub.lift σ : Sub S (b :: Γ) (b :: Δ)))
      (Sub.lift (Sub.transS G hC σ)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w =>
      change Sub.transS G hC (fun {_} u ↦ (σ u).rename Var.succ) w
        = (Sub.transS G hC σ w).rename Var.succ
      rw [transS_rename, Ren.mapTy_shift]

theorem nrmSub_commute (hC : G.Closed) (σ : Sub S Γ Δ) (b : Ty) :
    @Eq (Sub S (G.tr b :: List.map G.tr Γ) (G.tr b :: List.map G.tr Δ))
      (fun {_} v ↦ (Sub.lift (Sub.transS G hC σ) v).substitute (G.nrmSub b (List.map G.tr Δ)))
      (fun {_} v ↦ (G.nrmSub b (List.map G.tr Γ) v).substitute (Sub.lift (Sub.transS G hC σ))) := by
  funext c v
  cases v with
  | zero =>
      change (Term.var Var.zero : Term S (G.tr b :: List.map G.tr Δ) (G.tr b)).substitute
          (G.nrmSub b (List.map G.tr Δ))
        = (G.nrmTy b (Term.var Var.zero)).substitute (Sub.lift (Sub.transS G hC σ))
      rw [G.nrmTy_substitute]
      rfl
  | succ w =>
      change ((Sub.transS G hC σ w).rename Var.succ).substitute (G.nrmSub b (List.map G.tr Δ))
        = (Term.var (Var.succ w) : Term S (G.tr b :: List.map G.tr Γ) _).substitute
            (Sub.lift (Sub.transS G hC σ))
      rw [Term.substitute_rename]
      change (Sub.transS G hC σ w).substitute (fun v ↦ Term.var (Var.succ v)) = _
      rw [Term.substitute_var]
      rfl

theorem trans_substitute (hC : G.Closed) {a : Ty} (t : Term S Γ a) (σ : Sub S Γ Δ) :
    G.trans hC (t.substitute σ) = (G.trans hC t).substitute (Sub.transS G hC σ) := by
  induction t generalizing Δ with
  | var v => exact (transS_apply G hC σ v).symm
  | const c τ hτ =>
      simp only [trans, Term.substitute]
      rw [G.nrmTy_substitute, G.rawConst_substitute]
  | app f x ihf ihx => simp only [trans, Term.substitute, ihf, ihx]
  | lam b ih =>
      simp only [trans, Term.substitute]
      rw [ih, Term.substitute_substitute, Term.substitute_substitute]
      congr 2
      funext c v
      have h := congrFun (congrFun (G.nrmSub_commute hC σ _) c) v
      simp only [transS_lift]
      exact h
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [trans, Term.substitute, ihp, ihq]
  | imp p q ihp ihq => simp only [trans, Term.substitute, ihp, ihq]
  | all p ih =>
      simp only [trans, Term.substitute]
      rw [ih, Term.substitute_substitute, Term.substitute_substitute]
      congr 2
      funext c v
      have h := congrFun (congrFun (G.nrmSub_commute hC σ _) c) v
      simp only [transS_lift]
      exact h
  | ex p ih =>
      simp only [trans, Term.substitute]
      rw [ih, Term.substitute_substitute, Term.substitute_substitute]
      congr 2
      funext c v
      have h := congrFun (congrFun (G.nrmSub_commute hC σ _) c) v
      simp only [transS_lift]
      exact h
  | eq =>
      simp only [trans]
      rw [G.nrmTy_substitute]; rfl
  | choice =>
      simp only [trans]
      rw [G.nrmTy_substitute]; rfl

end TypeDefGate

end QEDFV.HOL
