import QEDFV.HOL.TdChain

/-! The oracle of a type definition with parameters: the normaliser at each instance of the new
type, built from the translated predicate at that instance. The construction is by recursion on
the nesting depth of the new constructor `k`; at depth above the current stage the oracle is
the identity, which is idempotent, so a derivation that does not use the laws of the new type
definition can be translated with every stage (`TdChain.hd_trans_chain`). -/
namespace QEDFV.HOL

/-- `Ty.KD k n e τ`: the nesting depth of the constructor `k` of arity `n` in `τ` is at most
`e`. -/
def Ty.KD (k n : Nat) : Nat → Ty → Prop
  | _, .bool => True
  | _, .ind => True
  | _, .var _ => True
  | e, .arr a b => Ty.KD k n e a ∧ Ty.KD k n e b
  | e, .con j m args =>
      if j = k ∧ m = n then
        (match e with
          | 0 => False
          | e' + 1 => ∀ i, Ty.KD k n e' (args i))
      else ∀ i, Ty.KD k n e (args i)

section KD

variable {k n : Nat}

theorem Ty.KD_con_pos {j m : Nat} (args : Fin m → Ty) (e : Nat) (hc : j = k ∧ m = n) :
    Ty.KD k n e (.con j m args) ↔
      (match e with | 0 => False | e' + 1 => ∀ i, Ty.KD k n e' (args i)) := by
  conv_lhs => rw [Ty.KD.eq_def]
  simp only [if_pos hc]

theorem Ty.KD_con_neg {j m : Nat} (args : Fin m → Ty) (e : Nat) (hc : ¬ (j = k ∧ m = n)) :
    Ty.KD k n e (.con j m args) ↔ ∀ i, Ty.KD k n e (args i) := by
  conv_lhs => rw [Ty.KD.eq_def]
  simp only [if_neg hc]

theorem Ty.KD_mono (a : Ty) : ∀ {e : Nat}, Ty.KD k n e a → Ty.KD k n (e + 1) a := by
  induction a with
  | bool => intro e _; trivial
  | ind => intro e _; trivial
  | var _ => intro e _; trivial
  | arr a b iha ihb => intro e h; exact ⟨iha h.1, ihb h.2⟩
  | con j m args ih =>
      intro e h
      by_cases hc : j = k ∧ m = n
      · rw [Ty.KD_con_pos args _ hc] at h ⊢
        cases e with
        | zero => exact h.elim
        | succ e' => exact fun i ↦ ih i (h i)
      · rw [Ty.KD_con_neg args _ hc] at h ⊢
        exact fun i ↦ ih i (h i)

theorem Ty.KD_of_le (a : Ty) {e e' : Nat} (h : Ty.KD k n e a) (hle : e ≤ e') :
    Ty.KD k n e' a := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Ty.KD_mono a ih

theorem Ty.KD_con_new (e : Nat) (args : Fin n → Ty) :
    Ty.KD k n (e + 1) (.con k n args) ↔ ∀ i, Ty.KD k n e (args i) := by
  rw [Ty.KD_con_pos args _ ⟨rfl, rfl⟩]

theorem Ty.KD_of_not_mem (a : Ty) (h : k ∉ a.tyCons) (e : Nat) : Ty.KD k n e a := by
  induction a generalizing e with
  | bool => trivial
  | ind => trivial
  | var _ => trivial
  | arr a b iha ihb =>
      simp only [Ty.tyCons, Set.mem_union, not_or] at h
      exact ⟨iha h.1 e, ihb h.2 e⟩
  | con j m args ih =>
      have hj : j ≠ k := fun e' ↦ h (by simp [Ty.tyCons, e'])
      rw [Ty.KD_con_neg args _ (fun hc ↦ hj hc.1)]
      exact fun i ↦ ih i (fun hi ↦ h (by simp only [Ty.tyCons]; exact Or.inr ⟨i, hi⟩)) e

theorem exists_bound (m : Nat) (f : Fin m → Nat) : ∃ E, ∀ i, f i ≤ E := by
  induction m with
  | zero => exact ⟨0, fun i ↦ i.elim0⟩
  | succ m ih =>
      obtain ⟨E, hE⟩ := ih (fun i ↦ f i.castSucc)
      refine ⟨max E (f (Fin.last m)), fun i ↦ ?_⟩
      induction i using Fin.lastCases with
      | last => exact Nat.le_max_right _ _
      | cast i => exact (hE i).trans (Nat.le_max_left _ _)

theorem Ty.exists_KD (a : Ty) : ∃ e, Ty.KD k n e a := by
  induction a with
  | bool => exact ⟨0, trivial⟩
  | ind => exact ⟨0, trivial⟩
  | var _ => exact ⟨0, trivial⟩
  | arr a b iha ihb =>
      obtain ⟨e1, h1⟩ := iha
      obtain ⟨e2, h2⟩ := ihb
      exact ⟨max e1 e2, Ty.KD_of_le a h1 (Nat.le_max_left _ _),
        Ty.KD_of_le b h2 (Nat.le_max_right _ _)⟩
  | con j m args ih =>
      choose f hf using ih
      obtain ⟨E, hE⟩ := exists_bound m f
      by_cases hc : j = k ∧ m = n
      · refine ⟨E + 1, ?_⟩
        rw [Ty.KD_con_pos args _ hc]
        exact fun i ↦ Ty.KD_of_le (args i) (hf i) (hE i)
      · refine ⟨E, ?_⟩
        rw [Ty.KD_con_neg args _ hc]
        exact fun i ↦ Ty.KD_of_le (args i) (hf i) (hE i)

/-- Substituting into a type free of `k` stays within the depth of the substituted types. -/
theorem Ty.KD_subst (a : Ty) (h : k ∉ a.tyCons) (θ : TypeSub) (e : Nat)
    (hθ : ∀ v, v ∈ a.typeVars → Ty.KD k n e (θ v)) : Ty.KD k n e (a.subst θ) := by
  induction a with
  | bool => trivial
  | ind => trivial
  | var i => exact hθ i (by simp [Ty.typeVars])
  | arr a b iha ihb =>
      simp only [Ty.tyCons, Set.mem_union, not_or] at h
      exact ⟨iha h.1 (fun v hv ↦ hθ v (Or.inl hv)), ihb h.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | con j m args ih =>
      have hj : j ≠ k := fun e' ↦ h (by simp [Ty.tyCons, e'])
      change Ty.KD k n e (.con j m (fun i ↦ (args i).subst θ))
      rw [Ty.KD_con_neg _ _ (fun hc ↦ hj hc.1)]
      exact fun i ↦ ih i (fun hi ↦ h (by simp only [Ty.tyCons]; exact Or.inr ⟨i, hi⟩))
        (fun v hv ↦ hθ v (by simp only [Ty.typeVars]; exact ⟨i, hv⟩))

end KD

/-- The annotation types of a term at which its translation uses the oracle have depth at
most `e`. -/
def Term.AnnKD {S : Signature} (k n e : Nat) : {Γ : List Ty} → {a : Ty} → Term S Γ a → Prop
  | _, _, .var _ => True
  | _, _, .const _ τ _ => Ty.KD k n e τ
  | _, _, .app f x => Term.AnnKD k n e f ∧ Term.AnnKD k n e x
  | _, _, @Term.lam _ a _ _ b => Ty.KD k n e a ∧ Term.AnnKD k n e b
  | _, _, .truth => True
  | _, _, .falsity => True
  | _, _, .conj p q => Term.AnnKD k n e p ∧ Term.AnnKD k n e q
  | _, _, .imp p q => Term.AnnKD k n e p ∧ Term.AnnKD k n e q
  | _, _, @Term.all _ a _ p => Ty.KD k n e a ∧ Term.AnnKD k n e p
  | _, _, @Term.ex _ a _ p => Ty.KD k n e a ∧ Term.AnnKD k n e p
  | _, _, @Term.eq _ _ a => Ty.KD k n e a
  | _, _, @Term.choice _ _ a => Ty.KD k n e a

theorem Term.AnnKD_instType {S : Signature} {k n e : Nat} {Γ : List Ty} {a : Ty}
    (t : Term S Γ a) (θ : TypeSub) (hk : k ∉ t.tyCons)
    (hθ : ∀ v, v ∈ t.annotVars → Ty.KD k n e (θ v)) : Term.AnnKD k n e (t.instType θ) := by
  induction t with
  | var v => trivial
  | const c τ h =>
      exact Ty.KD_subst τ hk θ e hθ
  | app f x ihf ihx =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨ihf hk.1 (fun v hv ↦ hθ v (Or.inl hv)), ihx hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | @lam a Γ b b0 ih =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨Ty.KD_subst a hk.1 θ e (fun v hv ↦ hθ v (Or.inl hv)),
        ih hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | truth => trivial
  | falsity => trivial
  | conj p q ihp ihq =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨ihp hk.1 (fun v hv ↦ hθ v (Or.inl hv)), ihq hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | imp p q ihp ihq =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨ihp hk.1 (fun v hv ↦ hθ v (Or.inl hv)), ihq hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | @all a Γ p ih =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨Ty.KD_subst a hk.1 θ e (fun v hv ↦ hθ v (Or.inl hv)),
        ih hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | @ex a Γ p ih =>
      simp only [Term.tyCons, Set.mem_union, not_or] at hk
      exact ⟨Ty.KD_subst a hk.1 θ e (fun v hv ↦ hθ v (Or.inl hv)),
        ih hk.2 (fun v hv ↦ hθ v (Or.inr hv))⟩
  | @eq Γ a =>
      simp only [Term.tyCons, Ty.tyCons, Set.mem_union, not_or] at hk
      exact Ty.KD_subst a hk.1 θ e (fun v hv ↦ hθ v (Or.inl hv))
  | @choice Γ a =>
      simp only [Term.tyCons, Ty.tyCons, Set.mem_union, not_or] at hk
      exact Ty.KD_subst a hk.1.1 θ e (fun v hv ↦ hθ v (Or.inl (Or.inl hv)))

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- The oracles agree on all types of depth at most `e`. -/
def AgreeUpTo (N N' : G.Oracle) (e : Nat) : Prop :=
  ∀ τ, Ty.KD G.k G.n e τ → N τ = N' τ

theorem nrmTy_congr_oracle {N N' : G.Oracle} {e : Nat} (hN : G.AgreeUpTo N N' e) (τ : Ty)
    (hτ : Ty.KD G.k G.n e τ) {Γ : List Ty} (u : Term S Γ (G.tr τ)) :
    G.nrmTy N τ u = G.nrmTy N' τ u := by
  induction τ generalizing Γ with
  | bool => rfl
  | ind => rfl
  | var _ => rfl
  | arr a b iha ihb =>
      by_cases hk : G.k ∈ (Ty.arr a b).tyCons
      · simp only [nrmTy, if_pos hk]
        rw [ihb hτ.2, iha hτ.1]
      · simp only [nrmTy, if_neg hk]
  | con j m args ih =>
      by_cases h : j = G.k ∧ m = G.n
      · simp only [nrmTy, h, and_self, if_true]
        rw [hN _ hτ]
      · simp only [nrmTy, h, if_false]

theorem nrmSub_congr_oracle {N N' : G.Oracle} {e : Nat} (hN : G.AgreeUpTo N N' e) (a : Ty)
    (ha : Ty.KD G.k G.n e a) (Γ : List Ty) :
    @Eq (Sub S (G.tr a :: Γ) (G.tr a :: Γ)) (G.nrmSub N a Γ) (G.nrmSub N' a Γ) := by
  funext c v
  cases v with
  | zero => exact G.nrmTy_congr_oracle hN a ha _
  | succ w => rfl

theorem trans_congr_oracle {N N' : G.Oracle} {e : Nat} (hN : G.AgreeUpTo N N' e)
    {Γ : List Ty} {a : Ty} (t : Term S Γ a) (ht : Term.AnnKD G.k G.n e t) :
    G.trans N t = G.trans N' t := by
  induction t with
  | var v => rfl
  | const c τ h => exact G.nrmTy_congr_oracle hN τ ht _
  | app f x ihf ihx => simp only [trans, ihf ht.1, ihx ht.2]
  | @lam a Γ b b0 ih =>
      simp only [trans, ih ht.2, G.nrmSub_congr_oracle hN a ht.1]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [trans, ihp ht.1, ihq ht.2]
  | imp p q ihp ihq => simp only [trans, ihp ht.1, ihq ht.2]
  | @all a Γ p ih => simp only [trans, ih ht.2, G.nrmSub_congr_oracle hN a ht.1]
  | @ex a Γ p ih => simp only [trans, ih ht.2, G.nrmSub_congr_oracle hN a ht.1]
  | @eq Γ a => exact G.nrmTy_congr_oracle hN (Ty.arr a (Ty.arr a Ty.bool)) ⟨ht, ht, trivial⟩ _
  | @choice Γ a => exact G.nrmTy_congr_oracle hN (Ty.arr (Ty.arr a Ty.bool) a) ⟨⟨ht, trivial⟩, ht⟩ _

/-! ### The staged oracle -/

/-- The arguments of an instance of the new type. -/
def newArgs (τ : Ty) : Option (Fin G.n → Ty) :=
  match τ with
  | .con j m args => if h : j = G.k ∧ m = G.n then some (h.2 ▸ args) else none
  | _ => none

theorem newArgs_con (args : Fin G.n → Ty) : G.newArgs (.con G.k G.n args) = some args := by
  simp [newArgs]

theorem eq_of_newArgs {τ : Ty} {args : Fin G.n → Ty} (h : G.newArgs τ = some args) :
    τ = .con G.k G.n args := by
  cases τ with
  | con j m a =>
      by_cases hc : j = G.k ∧ m = G.n
      · obtain ⟨hj, hm⟩ := hc
        subst hj; subst hm
        simp [newArgs] at h
        subst h
        rfl
      · simp [newArgs, hc] at h
  | _ => simp [newArgs] at h

/-- The predicate of the retraction at the arguments `args`: fixed by `NR` and satisfying the
translated predicate. -/
noncomputable def Qc (N : G.Oracle) (args : Fin G.n → Ty) (Γ : List Ty) :
    Term S Γ (.arr (G.RT args) .bool) :=
  Term.lam (Term.conj ((G.NR N args (Term.var Var.zero)).equal (Term.var Var.zero))
    (((G.QT N args).closedLift : Term S (G.RT args :: Γ) _).app (Term.var Var.zero)))

/-- The retraction data at the arguments `args`. -/
noncomputable def cfgA (N : G.Oracle) (args : Fin G.n → Ty) : NormCfg S :=
  ⟨G.RT args, G.Qc N args []⟩

/-- The normaliser of the retraction at `args`, read at the type `tr (k(args))`. -/
noncomputable def normOf (N : G.Oracle) (args : Fin G.n → Ty) :
    Term S [] (.arr (G.tr (.con G.k G.n args)) (G.tr (.con G.k G.n args))) :=
  (G.tr_new_eq args).symm ▸ (G.cfgA N args).normIn []

open Classical in
/-- One stage of the oracle: at the types of depth exactly `d + 1` with head `k`, replace the
value by the retraction built from the previous stage. -/
noncomputable def stepO (N : G.Oracle) (d : Nat) : G.Oracle := fun τ ↦
  match h : G.newArgs τ with
  | some args =>
      if Ty.KD G.k G.n (d + 1) τ ∧ ¬ Ty.KD G.k G.n d τ then
        (G.eq_of_newArgs h).symm ▸ G.normOf N args
      else N τ
  | none => N τ

/-- The stages of the oracle: the identity, then the retractions of depth `1, 2, …`. -/
noncomputable def oracleSeq : Nat → G.Oracle
  | 0 => fun _ ↦ Term.lam (Term.var Var.zero)
  | d + 1 => G.stepO (oracleSeq d) d

theorem oracleSeq_succ (d : Nat) : G.oracleSeq (d + 1) = G.stepO (G.oracleSeq d) d := rfl

theorem oracleSeq_succ_of_not {d : Nat} {τ : Ty}
    (h : ¬ (Ty.KD G.k G.n (d + 1) τ ∧ ¬ Ty.KD G.k G.n d τ)) :
    G.oracleSeq (d + 1) τ = G.oracleSeq d τ := by
  rw [G.oracleSeq_succ]
  unfold stepO
  split
  · rename_i args hs
    simp [h]
  · rfl

theorem oracleSeq_stable {τ : Ty} {d : Nat} (hτ : Ty.KD G.k G.n d τ) :
    ∀ j, d ≤ j → G.oracleSeq j τ = G.oracleSeq d τ := by
  intro j hj
  induction hj with
  | refl => rfl
  | step hle ih =>
      rename_i j'
      rw [G.oracleSeq_succ_of_not (fun hh ↦ hh.2 (Ty.KD_of_le τ hτ hle)), ih]

theorem oracleSeq_new {d : Nat} (args : Fin G.n → Ty)
    (h1 : Ty.KD G.k G.n (d + 1) (.con G.k G.n args)) (h2 : ¬ Ty.KD G.k G.n d (.con G.k G.n args)) :
    G.oracleSeq (d + 1) (.con G.k G.n args) = G.normOf (G.oracleSeq d) args := by
  rw [G.oracleSeq_succ]
  unfold stepO
  split
  · rename_i a hs
    have := G.newArgs_con args
    rw [this] at hs
    cases hs
    simp [h1, h2]
  · rename_i hs
    rw [G.newArgs_con args] at hs
    cases hs

/-! ### Dependence of the instance data on the oracle -/

section Congr

variable {N N' : G.Oracle} {args : Fin G.n → Ty}

theorem KD_repTy_canon {e : Nat} (hargs : ∀ i, Ty.KD G.k G.n e (args i)) :
    Ty.KD G.k G.n e (G.repTy.subst (G.canonSub args)) := by
  refine Ty.KD_subst G.repTy (fun h ↦ G.repTy_tyCons_ne G.k h rfl) _ e (fun v hv ↦ ?_)
  have hv' : v < G.n := G.repTy_typeVars_lt v hv
  simp only [canonSub, Ty.argsSub, hv', dite_true]
  exact hargs ⟨v, hv'⟩

theorem AnnKD_pred_canon {e : Nat} (hargs : ∀ i, Ty.KD G.k G.n e (args i)) :
    Term.AnnKD G.k G.n e (G.pred.instType (G.canonSub args)) := by
  refine Term.AnnKD_instType G.pred _ G.k_fresh (fun v hv ↦ ?_)
  have hv' : v < G.n := G.closed v hv
  simp only [canonSub, Ty.argsSub, hv', dite_true]
  exact hargs ⟨v, hv'⟩

theorem NK_congr_oracle {e : Nat} (hN : G.AgreeUpTo N N' (e + 1))
    (hargs : ∀ i, Ty.KD G.k G.n e (args i)) {Γ : List Ty} (x : Term S Γ (G.RT args)) :
    G.NK N args x = G.NK N' args x := by
  unfold NK
  rw [hN _ ((Ty.KD_con_new e args).2 hargs)]

theorem NR_congr_oracle {e : Nat} (hN : G.AgreeUpTo N N' e)
    (hargs : ∀ i, Ty.KD G.k G.n e (args i)) {Γ : List Ty} (x : Term S Γ (G.RT args)) :
    G.NR N args x = G.NR N' args x := by
  unfold NR
  rw [G.nrmTy_congr_oracle hN _ (G.KD_repTy_canon hargs)]

theorem QT_congr_oracle {e : Nat} (hN : G.AgreeUpTo N N' e)
    (hargs : ∀ i, Ty.KD G.k G.n e (args i)) : G.QT N args = G.QT N' args := by
  unfold QT
  rw [G.trans_congr_oracle hN _ (G.AnnKD_pred_canon hargs)]

theorem LawData_congr_oracle {es : List (ModelExtension S)} {e : Nat}
    (hN : G.AgreeUpTo N N' (e + 1)) (hargs : ∀ i, Ty.KD G.k G.n e (args i))
    (h : G.LawData N es args) : G.LawData N' es args := by
  have hN' : G.AgreeUpTo N N' e := fun τ hτ ↦ hN τ (Ty.KD_of_le τ hτ (Nat.le_succ e))
  have hQ := G.QT_congr_oracle hN' hargs
  refine ⟨fun L x ↦ ?_, fun L x ↦ ?_, fun L x h1 h2 ↦ ?_⟩
  · rw [← G.NK_congr_oracle hN hargs, ← G.NR_congr_oracle hN' hargs]
    exact h.rangeR L x
  · rw [← G.NK_congr_oracle hN hargs, ← hQ]
    exact h.rangeQ L x
  · rw [← G.NK_congr_oracle hN hargs]
    rw [← G.NR_congr_oracle hN' hargs] at h1
    rw [← hQ] at h2
    exact h.fix L x h1 h2

end Congr

/-! ### Laws from the retraction -/

section Retraction

variable {N : G.Oracle} {args : Fin G.n → Ty} {es : List (ModelExtension S)}

theorem NR_rename (N : G.Oracle) (args : Fin G.n → Ty) {Γ Δ : List Ty}
    (x : Term S Γ (G.RT args)) (r : Ren Γ Δ) :
    (G.NR N args x).rename r = G.NR N args (x.rename r) := by
  unfold NR
  rw [Term.rename_cast, G.nrmTy_rename N, Term.rename_cast]

theorem Qc_rename (N : G.Oracle) (args : Fin G.n → Ty) {Γ Δ : List Ty} (r : Ren Γ Δ) :
    (G.Qc N args Γ).rename r = G.Qc N args Δ := by
  unfold Qc
  simp only [Term.rename, Term.equal, G.NR_rename, Term.closedLift_rename]
  rfl

theorem Qc_eq (N : G.Oracle) (args : Fin G.n → Ty) (Γ : List Ty) :
    G.Qc N args Γ = ((G.Qc N args [] : Term S [] _).closedLift : Term S Γ _) :=
  (G.Qc_rename N args Ren.empty).symm

theorem holds_eq (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} (t : Term S Γ (G.RT args)) :
    (G.cfgA N args).holds' t = (G.Qc N args Γ).app t := by
  unfold NormCfg.holds'
  rw [NormCfg.predIn_eq, G.Qc_eq N args Γ]
  rfl

theorem Qc_beta (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty}
    {L : List (Term S Γ .bool)} (y : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := ((G.Qc N args Γ).app y).equal (Term.conj ((G.NR N args y).equal y) (((G.QT N args).closedLift : Term S Γ _).app y)) } := by
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.conj ((G.NR N args (Term.var Var.zero)).equal (Term.var Var.zero))
      (((G.QT N args).closedLift : Term S (G.RT args :: Γ) _).app (Term.var Var.zero))) y)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have hb : ((Term.conj ((G.NR N args (Term.var Var.zero)).equal (Term.var Var.zero))
      (((G.QT N args).closedLift : Term S (G.RT args :: Γ) _).app (Term.var Var.zero))).substitute
      (Sub.single y) : Term S Γ .bool)
      = Term.conj ((G.NR N args y).equal y) (((G.QT N args).closedLift : Term S Γ _).app y) := by
    simp only [Term.substitute, Term.equal, G.NR_substitute, Term.closedLift_substitute]
    rfl
  rw [hb] at b1
  exact b1

theorem cast_closedLift_app {A B : Ty} (e : A = B) {Γ : List Ty} (T : Term S [] (.arr B B))
    (x : Term S Γ B) :
    (e ▸ (((e.symm ▸ T : Term S [] (.arr A A)).closedLift : Term S Γ (.arr A A)).app
      (e.symm ▸ x)) : Term S Γ B) = (T.closedLift : Term S Γ (.arr B B)).app x := by
  subst e; rfl

theorem NK_normOf {M N' : G.Oracle} (hnew : N' (.con G.k G.n args) = G.normOf M args)
    {Γ : List Ty} (x : Term S Γ (G.RT args)) :
    G.NK N' args x = (G.cfgA M args).nrm x := by
  unfold NK
  rw [hnew]
  unfold normOf
  rw [cast_closedLift_app (G.tr_new_eq args)]
  unfold NormCfg.nrm
  rw [NormCfg.normIn_eq _ Γ]

theorem lawData_of_retraction {M N' : G.Oracle} {d : Nat} {wC : Term S [] (G.RT args)}
    (hargs : ∀ i, Ty.KD G.k G.n d (args i)) (hN'M : G.AgreeUpTo N' M d)
    (hnew : N' (.con G.k G.n args) = G.normOf M args)
    (hw : HistoryDerivation S es { hyps := [], concl := (G.Qc M args []).app wC }) :
    G.LawData N' es args := by
  have hNR := fun {Γ : List Ty} (x : Term S Γ (G.RT args)) ↦ G.NR_congr_oracle hN'M hargs x
  have hQ := G.QT_congr_oracle hN'M hargs
  have hrange : ∀ {Γ : List Ty} (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)),
      HistoryDerivation S es { hyps := L, concl := Term.conj ((G.NR M args ((G.cfgA M args).nrm x)).equal ((G.cfgA M args).nrm x)) (((G.QT M args).closedLift : Term S Γ _).app ((G.cfgA M args).nrm x)) } := by
    intro Γ L x
    have hr := ((G.cfgA M args).nrm_range hw x).mono (L := L) (fun _ hh ↦ by simp at hh)
    rw [G.holds_eq] at hr
    exact HistoryDerivation.eqMp' (G.Qc_beta M args _) hr
  refine ⟨fun L x ↦ ?_, fun L x ↦ ?_, fun L x h1 h2 ↦ ?_⟩
  · rw [G.NK_normOf hnew, hNR]
    exact HistoryDerivation.conjL (hrange L x)
  · rw [G.NK_normOf hnew, hQ]
    exact HistoryDerivation.conjR (hrange L x)
  · rw [hNR] at h1
    rw [hQ] at h2
    rw [G.NK_normOf hnew]
    have hq := HistoryDerivation.eqMp' (HistoryDerivation.sym (G.Qc_beta M args (es := es) (L := L) x))
      (HistoryDerivation.conjI h1 h2)
    have hf := ((G.cfgA M args).nrm_fix hw x).mono (L := (G.Qc M args _).app x :: L)
      (fun h hh ↦ by
        simp only [List.mem_singleton] at hh
        subst hh
        rw [G.holds_eq]
        exact List.mem_cons_self ..)
    exact HistoryDerivation.cut hq hf

theorem cast_app_closedLift {A B C : Ty} (e : A = B) {Γ : List Ty} (u : Term S [] (.arr A C))
    (x : Term S Γ B) :
    ((congrArg (fun X ↦ Ty.arr X C) e ▸ u : Term S [] (.arr B C)).closedLift :
      Term S Γ (.arr B C)).app x = (u.closedLift : Term S Γ (.arr A C)).app (e.symm ▸ x) := by
  subst e; rfl

theorem QTc_app (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} (x : Term S Γ (G.RT args)) :
    ((G.QT N args).closedLift : Term S Γ _).app x =
      ((G.trans N (G.pred.instType (G.canonSub args)) :
        Term S [] (G.tr ((Ty.arr G.repTy .bool).subst (G.canonSub args)))).closedLift :
        Term S Γ _).app ((G.tr_R_eq args).symm ▸ x :
          Term S Γ (G.tr (G.repTy.subst (G.canonSub args)))) := by
  unfold QT
  exact cast_app_closedLift (G.tr_R_eq args) _ x

/-- The translated predicate respects the normalisation at the representation type. -/
theorem Qinv (N : G.Oracle) (hI : G.Idem N es) (args : Fin G.n → Ty) {Γ : List Ty}
    (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := (((G.QT N args).closedLift : Term S Γ _).app (G.NR N args x)).equal (((G.QT N args).closedLift : Term S Γ _).app x) } := by
  rw [G.QTc_app, G.QTc_app]
  unfold NR
  rw [Term.cast_cast]
  set c := G.canonSub args
  set u : Term S [] (G.tr ((Ty.arr G.repTy .bool).subst c)) := G.trans N (G.pred.instType c) with hu
  have hfix := G.trans_fixed N hI (G.pred.instType c)
  have hfix' : HistoryDerivation S es { hyps := L, concl := (G.nrmTy N ((Ty.arr G.repTy .bool).subst c) (u.closedLift : Term S Γ _)).equal (u.closedLift : Term S Γ _) } := by
    have h1 := NormCfg.closedLift_derivable (Γ := Γ) (es := es) hfix
    have h2 : HistoryDerivation S es { hyps := [], concl := ((G.nrmTy N ((Ty.arr G.repTy .bool).subst c) u).closedLift : Term S Γ _).equal (u.closedLift : Term S Γ _) } := h1
    have e1 : ((G.nrmTy N ((Ty.arr G.repTy .bool).subst c) u).closedLift : Term S Γ _) = G.nrmTy N ((Ty.arr G.repTy .bool).subst c) (u.closedLift : Term S Γ _) :=
      G.nrmTy_rename N _ u _
    rw [e1] at h2
    exact h2.mono (fun _ hh ↦ by simp at hh)
  have hA := G.nrm_app (es := es) N (G.repTy.subst c) .bool (L := L) (u.closedLift : Term S Γ _)
    ((G.tr_R_eq args).symm ▸ x : Term S Γ (G.tr (G.repTy.subst c)))
  have hB := HistoryDerivation.mkComb' hfix' (HistoryDerivation.refl' (L := L)
    ((G.tr_R_eq args).symm ▸ x : Term S Γ (G.tr (G.repTy.subst c))))
  exact HistoryDerivation.trans' (HistoryDerivation.sym hA) hB

/-- A witness of the retraction predicate at `args`, from a witness of the gate's predicate
at the old history. -/
theorem witnessC (gs : List (TypeDefGate S))
    (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0) (hpair : List.Pairwise (Older (S := S)) gs)
    {M : G.Oracle} (hM : G.Idem M (gs.map ModelExtension.typeDefinition))
    (args : Fin G.n → Ty) {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      { hyps := [], concl := G.pred.app w }) :
    ∃ wC : Term S [] (G.RT args), HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      { hyps := [], concl := (G.Qc M args []).app wC } := by
  have hd := G.hd_trans_chain M gs hsc hpair hM hwit (Or.inr ⟨[], rfl⟩)
    (fun heq ↦ absurd heq (G.not_new_of_suffix gs ⟨[], rfl⟩)) (G.canonSub args)
  have hd' : HistoryDerivation S (gs.map ModelExtension.typeDefinition) { hyps := [], concl := (G.trans M (G.pred.instType (G.canonSub args))).app (G.trans M (w.instType (G.canonSub args))) } := hd
  set wC0 : Term S [] (G.RT args) := (G.tr_R_eq args) ▸ G.trans M (w.instType (G.canonSub args))
    with hwC0
  have hQ0 : HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      { hyps := [], concl := ((G.QT M args).closedLift : Term S [] _).app wC0 } := by
    rw [G.QTc_app, hwC0, Term.cast_cast, Term.closedLift_nil]
    exact hd'
  refine ⟨G.NR M args wC0, ?_⟩
  have hQ1 := HistoryDerivation.eqMp'
    (HistoryDerivation.sym (G.Qinv (es := gs.map ModelExtension.typeDefinition) M hM args [] wC0)) hQ0
  exact HistoryDerivation.eqMp'
    (HistoryDerivation.sym (G.Qc_beta (es := gs.map ModelExtension.typeDefinition) M args
      (L := []) (G.NR M args wC0)))
    (HistoryDerivation.conjI (G.NR_idem M hM args [] wC0) hQ1)

end Retraction

/-! ### The induction on the depth -/

section Induction

variable {es : List (ModelExtension S)}

theorem oracleSeq_succ_of_none {d : Nat} {τ : Ty} (h : G.newArgs τ = none) :
    G.oracleSeq (d + 1) τ = G.oracleSeq d τ := by
  rw [G.oracleSeq_succ]
  unfold stepO
  split
  · rename_i args hs
    rw [h] at hs
    cases hs
  · rfl

theorem agree_succ (d : Nat) : G.AgreeUpTo (G.oracleSeq (d + 1)) (G.oracleSeq d) d :=
  fun τ hτ ↦ G.oracleSeq_succ_of_not (fun hh ↦ hh.2 hτ)

/-- The identity at the translation of a type. -/
noncomputable def idL (τ : Ty) (Γ : List Ty) : Term S Γ (.arr (G.tr τ) (G.tr τ)) :=
  Term.lam (Term.var Var.zero)

theorem idem_idLam (es : List (ModelExtension S)) (τ : Ty) {Γ : List Ty}
    (L : List (Term S Γ .bool)) (u : Term S Γ (G.tr τ)) :
    HistoryDerivation S es { hyps := L, concl := ((G.idL τ Γ).app ((G.idL τ Γ).app u)).equal ((G.idL τ Γ).app u) } := by
  have hb := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.var Var.zero : Term S (G.tr τ :: Γ) (G.tr τ)) u)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.mkComb' (HistoryDerivation.refl' _) hb

theorem idem_of_lawData {N : G.Oracle} {args : Fin G.n → Ty} (h : G.LawData N es args)
    {Γ : List Ty} (L : List (Term S Γ .bool)) (u : Term S Γ (G.tr (.con G.k G.n args))) :
    HistoryDerivation S es { hyps := L, concl := (((N (.con G.k G.n args)).closedLift : Term S Γ _).app (((N (.con G.k G.n args)).closedLift : Term S Γ _).app u)).equal (((N (.con G.k G.n args)).closedLift : Term S Γ _).app u) } := by
  have := LawData.idem G h L ((G.tr_new_eq args) ▸ u)
  unfold NK at this
  simp only [Term.cast_cast] at this
  exact HistoryDerivation.cast_equal (G.tr_new_eq args).symm this |> fun d ↦ by
    simpa [Term.cast_cast] using d

theorem claim (gs : List (TypeDefGate S))
    (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0) (hpair : List.Pairwise (Older (S := S)) gs)
    {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      { hyps := [], concl := G.pred.app w }) :
    ∀ d : Nat, G.Idem (G.oracleSeq d) (gs.map ModelExtension.typeDefinition) ∧
      ∀ args : Fin G.n → Ty, Ty.KD G.k G.n d (.con G.k G.n args) →
        G.LawData (G.oracleSeq d) (gs.map ModelExtension.typeDefinition) args := by
  intro d
  induction d with
  | zero =>
      refine ⟨fun τ Γ L u ↦ G.idem_idLam _ τ L u, fun args h ↦ ?_⟩
      rw [Ty.KD_con_pos args 0 ⟨rfl, rfl⟩] at h
      exact h.elim
  | succ d ih =>
      obtain ⟨hIM, hLM⟩ := ih
      -- the laws at stage d + 1
      have hLaw : ∀ args : Fin G.n → Ty, Ty.KD G.k G.n (d + 1) (.con G.k G.n args) →
          G.LawData (G.oracleSeq (d + 1)) (gs.map ModelExtension.typeDefinition) args := by
        intro args h1
        by_cases h2 : Ty.KD G.k G.n d (.con G.k G.n args)
        · cases d with
          | zero =>
              rw [Ty.KD_con_pos args 0 ⟨rfl, rfl⟩] at h2
              exact h2.elim
          | succ e =>
              have hargs : ∀ i, Ty.KD G.k G.n e (args i) := (Ty.KD_con_new e args).1 h2
              refine G.LawData_congr_oracle (e := e) ?_ hargs (hLM args h2)
              intro τ hτ
              exact (G.agree_succ (e + 1) τ hτ).symm
        · have hargs : ∀ i, Ty.KD G.k G.n d (args i) := (Ty.KD_con_new d args).1 h1
          obtain ⟨wC, hw⟩ := G.witnessC gs hsc hpair hIM args hwit
          exact G.lawData_of_retraction hargs (G.agree_succ d) (G.oracleSeq_new args h1 h2) hw
      refine ⟨fun τ Γ L u ↦ ?_, hLaw⟩
      cases hs : G.newArgs τ with
      | none =>
          rw [G.oracleSeq_succ_of_none hs]
          exact hIM τ L u
      | some args =>
          have hτ := G.eq_of_newArgs hs
          by_cases hn : Ty.KD G.k G.n (d + 1) τ ∧ ¬ Ty.KD G.k G.n d τ
          · subst hτ
            exact G.idem_of_lawData (hLaw args hn.1) L u
          · rw [G.oracleSeq_succ_of_not hn]
            exact hIM τ L u

open Classical in
/-- Some stage at which a type has bounded depth. -/
noncomputable def kdep (τ : Ty) : Nat := Classical.choose (Ty.exists_KD (k := G.k) (n := G.n) τ)

theorem KD_kdep (τ : Ty) : Ty.KD G.k G.n (G.kdep τ) τ :=
  Classical.choose_spec (Ty.exists_KD (k := G.k) (n := G.n) τ)

/-- The oracle: at every type the value at a stage by which the type has bounded depth. -/
noncomputable def oracleStar : G.Oracle := fun τ ↦ G.oracleSeq (G.kdep τ) τ

theorem oracleStar_eq {τ : Ty} {d : Nat} (h : Ty.KD G.k G.n d τ) :
    G.oracleStar τ = G.oracleSeq d τ := by
  unfold oracleStar
  have h1 := G.oracleSeq_stable (G.KD_kdep τ) (max (G.kdep τ) d) (Nat.le_max_left _ _)
  have h2 := G.oracleSeq_stable h (max (G.kdep τ) d) (Nat.le_max_right _ _)
  exact h1.symm.trans h2

/-- **The oracle exists.** For a type definition whose predicate has a witness at the old
history, there is an oracle that is idempotent and has the laws of the retraction at every
instance. -/
theorem exists_oracle (gs : List (TypeDefGate S))
    (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0) (hpair : List.Pairwise (Older (S := S)) gs)
    {w : Term S [] G.repTy}
    (hwit : HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      { hyps := [], concl := G.pred.app w }) :
    ∃ N : G.Oracle, G.Idem N (gs.map ModelExtension.typeDefinition) ∧
      ∀ args : Fin G.n → Ty, G.LawData N (gs.map ModelExtension.typeDefinition) args := by
  refine ⟨G.oracleStar, fun τ Γ L u ↦ (G.claim gs hsc hpair hwit (G.kdep τ)).1 τ L u, ?_⟩
  intro args
  have hK := G.KD_kdep (.con G.k G.n args)
  cases hD : G.kdep (.con G.k G.n args) with
  | zero =>
      rw [hD, Ty.KD_con_pos args 0 ⟨rfl, rfl⟩] at hK
      exact hK.elim
  | succ e =>
      rw [hD] at hK
      have hargs : ∀ i, Ty.KD G.k G.n e (args i) := (Ty.KD_con_new e args).1 hK
      refine G.LawData_congr_oracle (e := e) ?_ hargs ((G.claim gs hsc hpair hwit (e + 1)).2 args hK)
      intro τ hτ
      exact (G.oracleStar_eq hτ).symm

end Induction

end TypeDefGate

end QEDFV.HOL
