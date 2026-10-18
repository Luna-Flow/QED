import QEDFV.HOL.TyConCongruence
import QEDFV.HOL.TypeDefGeneric

/-! Semantics of a type-definition gate, the model of `ks_register_type_definition`.

A gate names the new constructor `k` (arity `n`, parameters by index `0..n-1`), the
representation type `repTy`, the predicate `pred : repTy → bool`, and two fresh constants
`rep : k(α₀..αₙ₋₁) → repTy`, `abs : repTy → k(α₀..αₙ₋₁)` of the total signature `S`.

From an old model `(κ, I)` the gate builds a new model `(κ', I')`:
* `κ'` changes only the carrier of `k` at arity `n`: it is the predicate subtype of the
  representation type (evaluated in the old model, parameters at `as`, every other type
  variable at `PUnit`) when that predicate has a witness there, and `PUnit` otherwise;
* `I'` sends `rep` to the subtype projection and `abs` to the abstraction of
  `PredicateWitness.abs`, keeps the old value of every constant whose schema avoids `k`,
  and takes a canonical value elsewhere. -/
namespace QEDFV.HOL

variable {κ κ' : TyConVal}

/-- The valuation sending parameter `i < m` to `as i` and every other variable to `PUnit`. -/
def paramVal (m : Nat) (as : Fin m → Type) : TypeVal :=
  fun i ↦ if h : i < m then as ⟨i, h⟩ else PUnit

theorem paramVal_of_lt {m : Nat} (as : Fin m → Type) {i : Nat} (h : i < m) :
    paramVal m as i = as ⟨i, h⟩ := by
  simp [paramVal, h]

/-- The defined type `k(α₀, .., αₙ₋₁)`, parameters by index. -/
def paramTy (k n : Nat) : Ty := .con k n fun i ↦ .var i.val

/-- The gate of a type definition. Freshness of `k`, `rep` and `abs` with respect to a
declaration history is a premise of the derivation rule, not of the gate. `closed` is the
kernel's `tyvars ⊆ params` check, stated for `Term.annotVars` (every type annotation,
including binder domains, as the kernel's `term_tyvars` does). -/
structure TypeDefGate (S : Signature) where
  k : Nat
  n : Nat
  repTy : Ty
  pred : Term S [] (.arr repTy .bool)
  rep : Nat
  abs : Nat
  rep_ty : S rep = .arr (paramTy k n) repTy
  abs_ty : S abs = .arr repTy (paramTy k n)
  closed : ∀ i, i ∈ pred.annotVars → i < n
  k_fresh : k ∉ pred.tyCons
  rep_ne_abs : rep ≠ abs
  rep_fresh : rep ∉ pred.constIds
  abs_fresh : abs ∉ pred.constIds

theorem heq_choice {A B : Type} (hA : Nonempty A) (hB : Nonempty B) (h : A = B) :
    HEq (Classical.choice hA) (Classical.choice hB) := by
  subst h
  rfl

section Layer

variable {T T' E0 E0' E1 E1' : Type} {P0 : E0 → Prop} {P0' : E0' → Prop}

theorem layerRep_congr (hT : T = SubCarrier E0 P0) (hT' : T' = SubCarrier E0' P0')
    (e : E0 = E1) (e' : E0' = E1') {d : E1} {d' : E1'} (hTT : T = T') (h0 : E0 = E0')
    (h1 : E1 = E1') (hP : HEq P0 P0') (hd : HEq d d') :
    HEq (layerRep hT e d) (layerRep hT' e' d') := by
  subst hTT h0 h1
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hd
  rfl

theorem layerAbs_congr (hT : T = SubCarrier E0 P0) (hT' : T' = SubCarrier E0' P0')
    (e : E0 = E1) (e' : E0' = E1') (hTT : T = T') (h0 : E0 = E0')
    (h1 : E1 = E1') (hP : HEq P0 P0') :
    HEq (layerAbs hT e) (layerAbs hT' e') := by
  subst hTT h0 h1
  obtain rfl := eq_of_heq hP
  rfl

end Layer

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- The new type. -/
def newTy : Ty := paramTy G.k G.n

theorem repTy_typeVars_lt : ∀ i, i ∈ G.repTy.typeVars → i < G.n := fun i hi ↦
  G.closed i (G.pred.ty_annotVars_subset (Or.inl hi))

theorem repTy_tyCons_ne : ∀ j, j ∈ G.repTy.tyCons → j ≠ G.k := fun _ hj hjk ↦
  G.k_fresh (hjk ▸ G.pred.ty_tyCons_subset (Or.inl hj))

theorem pred_tyCons_ne : ∀ j, j ∈ G.pred.tyCons → j ≠ G.k := fun _ hj hjk ↦
  G.k_fresh (hjk ▸ hj)

/-- The predicate holds of `x` in the old model at the valuation `ρ`. -/
def holds (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ)
    (x : G.repTy.denote κ ρ) : Prop :=
  (G.pred.eval I ρ hρ closedEnv : G.repTy.denote κ ρ → Prop) x

/-- The predicate holds of `x` at `ρ` for some admissibility proof of `ρ`. -/
def holdsAny (I : ConstVal κ S) (ρ : TypeVal) (x : G.repTy.denote κ ρ) : Prop :=
  ∃ hρ : Admissible κ ρ, G.holds I ρ hρ x

/-- The old-model carrier of the new type at the parameters `as`. -/
noncomputable def carrier (I : ConstVal κ S) (m : Nat) (as : Fin m → Type) : Type :=
  SubCarrier (G.repTy.denote κ (paramVal m as)) (G.holdsAny I (paramVal m as))

open Classical in
/-- The new constructor interpretation. -/
noncomputable def newTyCon (I : ConstVal κ S) : TyConVal where
  carrier j m as := if j = G.k ∧ m = G.n then G.carrier I m as else κ.carrier j m as

theorem newTyCon_self (I : ConstVal κ S) (as : Fin G.n → Type) :
    (G.newTyCon I).carrier G.k G.n as = G.carrier I G.n as := by
  simp [newTyCon]

theorem newTyCon_of_ne (I : ConstVal κ S) {j : Nat} (hj : j ≠ G.k) (m : Nat)
    (as : Fin m → Type) : (G.newTyCon I).carrier j m as = κ.carrier j m as := by
  simp [newTyCon, hj]

theorem agreeOn_new (I : ConstVal κ S) {C : Set Nat} (hC : ∀ j, j ∈ C → j ≠ G.k) :
    κ.AgreeOn C (G.newTyCon I) :=
  fun j hj m as ↦ (G.newTyCon_of_ne I (hC j hj) m as).symm

theorem newTyCon_isAdmissible (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    (G.newTyCon I).IsAdmissible := by
  intro j m as has
  by_cases h : j = G.k ∧ m = G.n
  · obtain ⟨rfl, rfl⟩ := h
    rw [newTyCon_self]
    exact SubCarrier.nonempty _ _
  · have : (G.newTyCon I).carrier j m as = κ.carrier j m as := by
      simp [newTyCon, h]
    rw [this]
    exact hκ j m as has

theorem admissible_new_iff (hκ : κ.IsAdmissible) (I : ConstVal κ S) (ρ : TypeVal) :
    Admissible κ ρ ↔ Admissible (G.newTyCon I) ρ :=
  admissible_iff_of_isAdmissible hκ (G.newTyCon_isAdmissible hκ I) ρ

/-- The parameters of `ρ`. -/
def params (ρ : TypeVal) : Fin G.n → Type := fun j ↦ ρ j.val

/-- The valuation at which the old model is consulted. -/
def rho0 (ρ : TypeVal) : TypeVal := paramVal G.n (G.params ρ)

theorem rho0_of_lt (ρ : TypeVal) {i : Nat} (h : i < G.n) : G.rho0 ρ i = ρ i :=
  paramVal_of_lt _ h

theorem admissible_rho0 (hκ : κ.IsAdmissible) {ρ : TypeVal} (hρ : ∀ i, Nonempty (ρ i)) :
    Admissible κ (G.rho0 ρ) := by
  refine ⟨fun i ↦ ?_, hκ⟩
  by_cases h : i < G.n
  · rw [G.rho0_of_lt ρ h]
    exact hρ i
  · simp only [rho0, paramVal, h, dif_neg, not_false_eq_true]
    exact ⟨PUnit.unit⟩

/-- The representation type is the same in the old model at `rho0` and in the new model. -/
theorem repEq (I : ConstVal κ S) (ρ : TypeVal) :
    G.repTy.denote κ (G.rho0 ρ) = G.repTy.denote (G.newTyCon I) ρ :=
  G.repTy.denote_congr_gen (Set.Iio G.n) {j | j ≠ G.k}
    (fun _ hi ↦ G.rho0_of_lt ρ hi)
    (G.agreeOn_new I fun _ hj ↦ hj) (fun i hi ↦ G.repTy_typeVars_lt i hi)
    (fun j hj ↦ G.repTy_tyCons_ne j hj)

/-- The new carrier is the old-model subtype. -/
theorem carrierEq (I : ConstVal κ S) (ρ : TypeVal) :
    G.newTy.denote (G.newTyCon I) ρ =
      SubCarrier (G.repTy.denote κ (G.rho0 ρ)) (G.holdsAny I (G.rho0 ρ)) :=
  G.newTyCon_self I (G.params ρ)

/-- `Rep` in the new model. -/
noncomputable def repVal (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible (G.newTyCon I) ρ) :
    (Ty.arr G.newTy G.repTy).denote (G.newTyCon I) ρ :=
  layerRep (G.carrierEq I ρ) (G.repEq I ρ)
    (Classical.choice (G.repTy.carrier_nonempty _ ρ hρ))

/-- `Abs` in the new model. -/
noncomputable def absVal (I : ConstVal κ S) (ρ : TypeVal) :
    (Ty.arr G.repTy G.newTy).denote (G.newTyCon I) ρ :=
  layerAbs (G.carrierEq I ρ) (G.repEq I ρ)

/-- A type avoiding the constructor `k` has the same denotation in the old and new model. -/
theorem denote_old (I : ConstVal κ S) (a : Ty) (h : G.k ∉ a.tyCons) (ρ : TypeVal) :
    a.denote κ ρ = a.denote (G.newTyCon I) ρ :=
  a.denote_congr_gen Set.univ {j | j ≠ G.k} (fun _ _ ↦ rfl)
    (G.agreeOn_new I fun _ hj ↦ hj) (Set.subset_univ _) (fun _ hj hjk ↦ h (hjk ▸ hj))

open Classical in
/-- The new interpretation of the constants other than `rep`, `abs`. -/
noncomputable def baseConst (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    ConstVal (G.newTyCon I) S :=
  fun ρ hρ c ↦
    if h : G.k ∉ (S c).tyCons then
      cast (G.denote_old I (S c) h ρ) (I ρ ((G.admissible_new_iff hκ I ρ).mpr hρ) c)
    else Classical.choice ((S c).carrier_nonempty _ ρ hρ)

/-- The new constant interpretation. -/
noncomputable def newConst (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    ConstVal (G.newTyCon I) S :=
  ConstVal.override
    (ConstVal.override (G.baseConst hκ I) G.rep
      (fun ρ hρ ↦ cast (congrArg (Ty.denote (G.newTyCon I) ρ) G.rep_ty.symm) (G.repVal I ρ hρ)))
    G.abs (fun ρ _ ↦ cast (congrArg (Ty.denote (G.newTyCon I) ρ) G.abs_ty.symm) (G.absVal I ρ))


theorem newConst_rep (hκ : κ.IsAdmissible) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible (G.newTyCon I) ρ) :
    G.newConst hκ I ρ hρ G.rep =
      cast (congrArg (Ty.denote (G.newTyCon I) ρ) G.rep_ty.symm) (G.repVal I ρ hρ) := by
  unfold newConst
  rw [ConstVal.override_agree _ G.abs G.rep _ G.rep_ne_abs, ConstVal.override_value]

theorem newConst_abs (hκ : κ.IsAdmissible) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible (G.newTyCon I) ρ) :
    G.newConst hκ I ρ hρ G.abs =
      cast (congrArg (Ty.denote (G.newTyCon I) ρ) G.abs_ty.symm) (G.absVal I ρ) := by
  unfold newConst
  rw [ConstVal.override_value]

theorem newConst_old (hκ : κ.IsAdmissible) (I : ConstVal κ S) {c : Nat} (hr : c ≠ G.rep)
    (ha : c ≠ G.abs) (hk : G.k ∉ (S c).tyCons) (ρ : TypeVal)
    (hρ : Admissible (G.newTyCon I) ρ) :
    G.newConst hκ I ρ hρ c =
      cast (G.denote_old I (S c) hk ρ) (I ρ ((G.admissible_new_iff hκ I ρ).mpr hρ) c) := by
  unfold newConst
  rw [ConstVal.override_agree _ G.abs c _ ha, ConstVal.override_agree _ G.rep c _ hr]
  unfold baseConst
  rw [dif_pos hk]

theorem newTy_typeVars_lt : ∀ i, i ∈ G.newTy.typeVars → i < G.n := by
  intro i hi
  obtain ⟨j, hj⟩ := hi
  have : i = j.val := by simpa [Ty.typeVars] using hj
  exact this ▸ j.isLt

theorem lt_mem_rep_typeVars {i : Nat} (h : i < G.n) : i ∈ (S G.rep).typeVars := by
  rw [G.rep_ty]
  exact Or.inl ⟨⟨i, h⟩, by simp [Ty.typeVars]⟩

theorem lt_mem_abs_typeVars {i : Nat} (h : i < G.n) : i ∈ (S G.abs).typeVars := by
  rw [G.abs_ty]
  exact Or.inr ⟨⟨i, h⟩, by simp [Ty.typeVars]⟩

theorem rho0_congr {ρ ρ' : TypeVal} (h : ∀ i, i < G.n → ρ i = ρ' i) : G.rho0 ρ = G.rho0 ρ' := by
  funext i
  by_cases hi : i < G.n
  · rw [G.rho0_of_lt ρ hi, G.rho0_of_lt ρ' hi]
    exact h i hi
  · simp [rho0, paramVal, hi]

/-- `Rep` depends on the valuation only through the type parameters. -/
theorem repVal_heq (I : ConstVal κ S) {ρ ρ' : TypeVal} (hρ : Admissible (G.newTyCon I) ρ)
    (hρ' : Admissible (G.newTyCon I) ρ') (h : ∀ i, i < G.n → ρ i = ρ' i) :
    HEq (G.repVal I ρ hρ) (G.repVal I ρ' hρ') := by
  have hr := G.rho0_congr h
  unfold repVal
  refine layerRep_congr _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · exact G.newTy.denote_congr_vars _ fun i hi ↦ h i (G.newTy_typeVars_lt i hi)
  · rw [hr]
  · exact G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi)
  · rw [hr]
  · exact heq_choice _ _
      (G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi))

/-- `Abs` depends on the valuation only through the type parameters. -/
theorem absVal_heq (I : ConstVal κ S) {ρ ρ' : TypeVal}
    (h : ∀ i, i < G.n → ρ i = ρ' i) : HEq (G.absVal I ρ) (G.absVal I ρ') := by
  have hr := G.rho0_congr h
  unfold absVal
  refine layerAbs_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact G.newTy.denote_congr_vars _ fun i hi ↦ h i (G.newTy_typeVars_lt i hi)
  · rw [hr]
  · exact G.repTy.denote_congr_vars _ fun i hi ↦ h i (G.repTy_typeVars_lt i hi)
  · rw [hr]

theorem newConst_local_rep (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    (G.newConst hκ I).Local G.rep := by
  intro ρ hρ ρ' hρ' hag
  rw [G.newConst_rep hκ I ρ hρ, G.newConst_rep hκ I ρ' hρ']
  exact (cast_heq _ _).trans
    ((G.repVal_heq I hρ hρ' fun i hi ↦ hag i (G.lt_mem_rep_typeVars hi)).trans
      (cast_heq _ _).symm)

theorem newConst_local_abs (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    (G.newConst hκ I).Local G.abs := by
  intro ρ hρ ρ' hρ' hag
  rw [G.newConst_abs hκ I ρ hρ, G.newConst_abs hκ I ρ' hρ']
  exact (cast_heq _ _).trans ((G.absVal_heq I fun i hi ↦ hag i (G.lt_mem_abs_typeVars hi)).trans
    (cast_heq _ _).symm)

/-- The constant `rep` as a term. -/
def repTerm {Γ : List Ty} : Term S Γ (.arr G.newTy G.repTy) :=
  .const G.rep _ (G.rep_ty ▸ Ty.IsInst.refl _)

/-- The constant `abs` as a term. -/
def absTerm {Γ : List Ty} : Term S Γ (.arr G.repTy G.newTy) :=
  .const G.abs _ (G.abs_ty ▸ Ty.IsInst.refl _)

/-- The predicate in an arbitrary context. -/
def predIn (Γ : List Ty) : Term S Γ (.arr G.repTy .bool) :=
  G.pred.rename (fun {_} v ↦ by cases v)

theorem eval_repTerm (hκ : κ.IsAdmissible) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible (G.newTyCon I) ρ) {Γ : List Ty} (η : Env (G.newTyCon I) ρ Γ) :
    (G.repTerm (Γ := Γ)).eval (G.newConst hκ I) ρ hρ η = G.repVal I ρ hρ := by
  have hraw := eval_const_self (G.newConst hκ I) (G.newConst_local_rep hκ I) G.rep_ty
    (G.rep_ty ▸ Ty.IsInst.refl _) ρ hρ η
  have hv : HEq (G.newConst hκ I ρ hρ G.rep) (G.repVal I ρ hρ) := by
    rw [G.newConst_rep]
    exact cast_heq _ _
  exact eq_of_heq (hraw.trans hv)

theorem eval_absTerm (hκ : κ.IsAdmissible) (I : ConstVal κ S) (ρ : TypeVal)
    (hρ : Admissible (G.newTyCon I) ρ) {Γ : List Ty} (η : Env (G.newTyCon I) ρ Γ) :
    (G.absTerm (Γ := Γ)).eval (G.newConst hκ I) ρ hρ η = G.absVal I ρ := by
  have hraw := eval_const_self (G.newConst hκ I) (G.newConst_local_abs hκ I) G.abs_ty
    (G.abs_ty ▸ Ty.IsInst.refl _) ρ hρ η
  have hv : HEq (G.newConst hκ I ρ hρ G.abs) (G.absVal I ρ) := by
    rw [G.newConst_abs]
    exact cast_heq _ _
  exact eq_of_heq (hraw.trans hv)

theorem eval_predIn (J : ConstVal κ' S) (ρ : TypeVal) (hρ : Admissible κ' ρ) {Γ : List Ty}
    (η : Env κ' ρ Γ) :
    (G.predIn Γ).eval J ρ hρ η = G.pred.eval J ρ hρ closedEnv := by
  unfold predIn
  rw [Term.eval_rename]
  congr 1
  funext a v
  cases v


/-- `heq` of two predicates over equal types gives equal values along the cast. -/
theorem pred_cast_of_heq {A B : Type} (e : A = B) {f : A → Prop} {g : B → Prop}
    (h : HEq f g) (x : A) : f x = g (cast e x) := by
  subst e
  exact congrFun (eq_of_heq h) x

/-- Local interpretation (`ConstVal.Local`) of the constants of the predicate: the
semantic counterpart of `Term.annotVars`-closedness for a gate. -/
def PredLocal (I : ConstVal κ S) : Prop := ∀ c, c ∈ G.pred.constIds → I.Local c

/-- On a constant that is not `rep`/`abs` and whose schema avoids `k`, the new interpretation
agrees with the old one wherever the instance avoids `C` (a set of constructor ids that
excludes `k`), provided the old value is local. -/
theorem agreeAt_new (hκ : κ.IsAdmissible) (I : ConstVal κ S) {c : Nat} (hr : c ≠ G.rep)
    (ha : c ≠ G.abs) (hloc : I.Local c) {C : Set Nat} (hC : ∀ j, j ∈ C → j ≠ G.k) :
    I.AgreeAt (G.newConst hκ I) C c := by
  intro ρ hρ hρ' σ hσ
  have hk : G.k ∉ (S c).tyCons := by
    intro hkc
    have : G.k ∈ ((S c).subst σ).tyCons := by
      rw [Ty.tyCons_subst]
      exact Or.inl hkc
    exact hC G.k (hσ this) rfl
  have hpull : Admissible (G.newTyCon I) (σ.pull κ ρ) :=
    (G.admissible_new_iff hκ I _).mp (σ.pull_admissible κ ρ hρ)
  have hnew : Admissible (G.newTyCon I) (σ.pull (G.newTyCon I) ρ) :=
    σ.pull_admissible _ ρ hρ'
  rw [G.newConst_old hκ I hr ha hk _ hnew]
  refine HEq.trans ?_ (cast_heq _ _).symm
  apply hloc
  intro i hi
  have hσi : (σ i).tyCons ⊆ C := by
    intro j hj
    apply hσ
    rw [Ty.tyCons_subst]
    exact Or.inr ⟨i, hi, hj⟩
  exact (σ i).denote_congr_gen Set.univ C (fun _ _ ↦ rfl) (G.agreeOn_new I hC)
    (Set.subset_univ _) hσi

/-- **Old-language transport for a type-definition step.** A sequent that does not mention
the new constructor, `rep` or `abs` is valid in the new model iff it is valid in the old one.
Locality of the old interpretation on the constants of the sequent is needed because the
agreement of two models is compared at valuations that differ in the type variables a
constant does not depend on (`ConstVal.Local`). -/
theorem valid_iff_old (hκ : κ.IsAdmissible) (I : ConstVal κ S) {Γ : List Ty}
    (s : Sequent S Γ) (hk : G.k ∉ s.tyCons) (hr : G.rep ∉ s.constIds)
    (ha : G.abs ∉ s.constIds) (hloc : ∀ c, c ∈ s.constIds → I.Local c) :
    Valid (G.newConst hκ I) s ↔ Valid I s := by
  have hC : ∀ j, j ∈ s.tyCons → j ≠ G.k := fun j hj hjk ↦ hk (hjk ▸ hj)
  refine (valid_iff_κ I (G.newConst hκ I) (G.admissible_new_iff hκ I)
    (G.agreeOn_new I hC) fun c hc ↦ ?_).symm
  exact G.agreeAt_new hκ I (fun h ↦ hr (h ▸ hc)) (fun h ↦ ha (h ▸ hc)) (hloc c hc) hC

/-- The semantic counterpart of the witness derivation `⊢ P w`: the predicate has a witness
at every admissible valuation of the old model. -/
def WitnessAt (I : ConstVal κ S) : Prop :=
  ∀ (ρ : TypeVal) (hρ : Admissible κ ρ), ∃ x, G.holds I ρ hρ x

/-- A closed term `w` with `P w` valid (hypothesis-free) gives a witness at every valuation.
This is how a derivation `⊢ P w` discharges `WitnessAt` through `derivation_sound`. -/
theorem witnessAt_of_valid (I : ConstVal κ S) (w : Term S [] G.repTy)
    (h : Valid I { hyps := [], concl := G.pred.app w }) : G.WitnessAt I := by
  intro ρ hρ
  refine ⟨w.eval I ρ hρ closedEnv, ?_⟩
  exact h ρ hρ closedEnv (fun _ hh ↦ nomatch hh)

/-- The old-model predicate and the new-model predicate correspond along the cast of the
representation type. -/
theorem holdsAny_iff (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hloc : G.PredLocal I)
    (ρ : TypeVal) (hρ : Admissible (G.newTyCon I) ρ) (x : G.repTy.denote κ (G.rho0 ρ)) :
    G.holdsAny I (G.rho0 ρ) x ↔
      (G.pred.eval (G.newConst hκ I) ρ hρ closedEnv : G.repTy.denote (G.newTyCon I) ρ → Prop)
        (cast (G.repEq I ρ) x) := by
  have hA : Admissible κ (G.rho0 ρ) := G.admissible_rho0 hκ hρ.var
  have hheq : HEq (G.pred.eval (G.newConst hκ I) ρ hρ closedEnv)
      (G.pred.eval I (G.rho0 ρ) hA closedEnv) := by
    refine Term.eval_congr (Set.Iio G.n) {j | j ≠ G.k} G.pred.constIds hρ hA
      (fun i hi ↦ (G.rho0_of_lt ρ hi).symm) (G.agreeOn_new I fun _ hj ↦ hj).symm ?_
      G.pred G.closed (fun j hj ↦ G.pred_tyCons_ne j hj) (fun _ h ↦ h) _ _
      (fun _ v _ _ ↦ nomatch v)
    intro c hc τ hτ hτv hτc
    have hspec := Ty.constSub_spec (S c) τ hτ
    generalize Ty.constSub (S c) τ hτ = σ at hspec ⊢
    have hσv : ((S c).subst σ).typeVars ⊆ Set.Iio G.n := hspec ▸ hτv
    have hσc : ((S c).subst σ).tyCons ⊆ {j | j ≠ G.k} := hspec ▸ hτc
    have hr : c ≠ G.rep := fun h ↦ G.rep_fresh (h ▸ hc)
    have ha : c ≠ G.abs := fun h ↦ G.abs_fresh (h ▸ hc)
    have hk : G.k ∉ (S c).tyCons := by
      intro hkc
      have : G.k ∈ ((S c).subst σ).tyCons := by
        rw [Ty.tyCons_subst]
        exact Or.inl hkc
      exact hσc this rfl
    have hnew : Admissible (G.newTyCon I) (σ.pull (G.newTyCon I) ρ) :=
      σ.pull_admissible _ ρ hρ
    rw [G.newConst_old hκ I hr ha hk _ hnew]
    refine (cast_heq _ _).trans (hloc c hc _ _ _ _ ?_)
    intro i hi
    have hσi : (σ i).typeVars ⊆ Set.Iio G.n := by
      intro j hj
      apply hσv
      rw [Ty.typeVars_subst]
      exact ⟨i, hi, hj⟩
    have hσi' : (σ i).tyCons ⊆ {j | j ≠ G.k} := by
      intro j hj
      apply hσc
      rw [Ty.tyCons_subst]
      exact Or.inr ⟨i, hi, hj⟩
    exact (σ i).denote_congr_gen (Set.Iio G.n) {j | j ≠ G.k}
      (fun i hi ↦ (G.rho0_of_lt ρ hi).symm) (G.agreeOn_new I fun _ hj ↦ hj).symm hσi hσi'
  have key := pred_cast_of_heq (G.repEq I ρ) hheq.symm x
  rw [← key]
  constructor
  · rintro ⟨hρ0, hx⟩
    exact hx
  · intro hx
    exact ⟨hA, hx⟩


/-! ### The three laws as sequents about `Rep` and `Abs` terms -/

/-- `⊢ Abs (Rep a) = a`, in the context `a : k(α)`. -/
def absRepSequent : Sequent S [G.newTy] :=
  { hyps := []
  , concl := (G.absTerm.app (G.repTerm.app (Term.var Var.zero))).equal (Term.var Var.zero) }

/-- `⊢ P (Rep a)`, in the context `a : k(α)`. -/
def repRangeSequent : Sequent S [G.newTy] :=
  { hyps := []
  , concl := (G.predIn [G.newTy]).app (G.repTerm.app (Term.var Var.zero)) }

/-- `P r ⊢ Rep (Abs r) = r`, in the context `r : repTy`. -/
def repAbsSequent : Sequent S [G.repTy] :=
  { hyps := [(G.predIn [G.repTy]).app (Term.var Var.zero)]
  , concl := (G.repTerm.app (G.absTerm.app (Term.var Var.zero))).equal (Term.var Var.zero) }

/-- Law 1, `Abs (Rep a) = a`, holds in the new model without any witness: without a
witness the new carrier is `PUnit`. -/
theorem valid_absRep (hκ : κ.IsAdmissible) (I : ConstVal κ S) :
    Valid (G.newConst hκ I) G.absRepSequent := by
  intro ρ hρ η _
  change G.absTerm.eval (G.newConst hκ I) ρ hρ η
      (G.repTerm.eval (G.newConst hκ I) ρ hρ η (η _ Var.zero)) = η _ Var.zero
  rw [G.eval_absTerm, G.eval_repTerm]
  exact layer_abs_rep (G.carrierEq I ρ) (G.repEq I ρ) _ _

/-- Law 2, `P (Rep a)`. This is the law that needs the witness: the hypothesis `hW` is the
semantic form of the hypothesis-free derivation `⊢ P w` required by the kernel. -/
theorem valid_repRange (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hloc : G.PredLocal I)
    (hW : G.WitnessAt I) : Valid (G.newConst hκ I) G.repRangeSequent := by
  intro ρ hρ η _
  change (G.predIn [G.newTy]).eval (G.newConst hκ I) ρ hρ η
      (G.repTerm.eval (G.newConst hκ I) ρ hρ η (η _ Var.zero))
  rw [G.eval_predIn, G.eval_repTerm]
  have hA : Admissible κ (G.rho0 ρ) := G.admissible_rho0 hκ hρ.var
  obtain ⟨x, hx⟩ := hW _ hA
  exact layer_pred_rep (G.carrierEq I ρ) (G.repEq I ρ) _
    (fun x ↦ G.holdsAny_iff hκ I hloc ρ hρ x) ⟨x, hA, hx⟩ _

/-- Law 3, `P r ⊢ Rep (Abs r) = r`. No witness hypothesis is needed: the premise `P r`
is itself a witness. -/
theorem valid_repAbs (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hloc : G.PredLocal I) :
    Valid (G.newConst hκ I) G.repAbsSequent := by
  intro ρ hρ η hh
  have hP := hh _ (List.mem_singleton.mpr rfl)
  change (G.predIn [G.repTy]).eval (G.newConst hκ I) ρ hρ η (η _ Var.zero) at hP
  rw [G.eval_predIn] at hP
  change G.repTerm.eval (G.newConst hκ I) ρ hρ η
      (G.absTerm.eval (G.newConst hκ I) ρ hρ η (η _ Var.zero)) = η _ Var.zero
  rw [G.eval_absTerm, G.eval_repTerm]
  exact layer_rep_abs (G.carrierEq I ρ) (G.repEq I ρ) _
    (fun x ↦ G.holdsAny_iff hκ I hloc ρ hρ x) hP


/-! ### Connection to the carrier-level contract

With a witness at the old model, the gate yields a `PredicateFamily` (hence a
`TypeDefContract`) of `HOL/TypeDefinitions.lean`; the new carrier is its predicate subtype
and `Rep` is its `Subtype.val`. -/

/-- The predicate family of the gate at an old model with a witness. -/
def family (I : ConstVal κ S) (hW : G.WitnessAt I) : PredicateFamily κ where
  repTy := G.repTy
  pred := G.holds I
  witness := hW

/-- The carrier-level type-definition contract of the gate. -/
def contract (I : ConstVal κ S) (hW : G.WitnessAt I) : TypeDefContract κ :=
  ⟨G.family I hW⟩

theorem holdsAny_eq_holds (I : ConstVal κ S) {ρ : TypeVal} (hρ : Admissible κ ρ) :
    G.holdsAny I ρ = G.holds I ρ hρ := by
  funext x
  exact propext ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hρ, h⟩⟩

/-- With a witness, the new carrier is the predicate subtype of the family. -/
theorem carrierEqFamily (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hW : G.WitnessAt I)
    (ρ : TypeVal) (hρ : Admissible (G.newTyCon I) ρ) :
    G.newTy.denote (G.newTyCon I) ρ =
      Subtype ((G.family I hW).pred (G.rho0 ρ) (G.admissible_rho0 hκ hρ.var)) := by
  have hA := G.admissible_rho0 hκ hρ.var
  have hex : ∃ x, G.holdsAny I (G.rho0 ρ) x := by
    obtain ⟨x, hx⟩ := hW _ hA
    exact ⟨x, hA, hx⟩
  rw [G.carrierEq I ρ, SubCarrier.eq_subtype hex, G.holdsAny_eq_holds I hA]
  rfl

theorem val_cast_congr {T α : Type} {P Q : α → Prop} (h1 : T = Subtype P) (hPQ : P = Q)
    (x : T) : (cast (h1.trans (congrArg Subtype hPQ)) x).1 = (cast h1 x).1 := by
  subst hPQ
  rfl

/-- With a witness, the new `Rep` is `Subtype.val` of the family subtype (along the cast of
the representation type). -/
theorem repVal_eq_val (hκ : κ.IsAdmissible) (I : ConstVal κ S) (hW : G.WitnessAt I)
    (ρ : TypeVal) (hρ : Admissible (G.newTyCon I) ρ) (x : G.newTy.denote (G.newTyCon I) ρ) :
    G.repVal I ρ hρ x =
      cast (G.repEq I ρ) (cast (G.carrierEqFamily hκ I hW ρ hρ) x).1 := by
  have hA := G.admissible_rho0 hκ hρ.var
  have hex : ∃ x, G.holdsAny I (G.rho0 ρ) x := by
    obtain ⟨x, hx⟩ := hW _ hA
    exact ⟨x, hA, hx⟩
  have h1 := G.carrierEq I ρ
  have key : G.carrierEqFamily hκ I hW ρ hρ =
      ((G.carrierEq I ρ).trans (SubCarrier.eq_subtype hex)).trans
        (congrArg Subtype (G.holdsAny_eq_holds I hA)) := rfl
  rw [key, val_cast_congr _ (G.holdsAny_eq_holds I hA)]
  unfold repVal layerRep
  rw [SubCarrier.rep_eq_witness hex]
  simp only [cast_cast]
  rfl

end TypeDefGate

end QEDFV.HOL
