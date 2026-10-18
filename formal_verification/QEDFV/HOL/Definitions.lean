import QEDFV.HOL.Transport

namespace QEDFV.HOL

variable {κ : TyConVal}

def closedEnv {ρ : TypeVal} : Env κ ρ [] := fun _ v ↦ by cases v

/-- The gate of a constant definition. `typeVarsClosed` is the kernel's check
`term_tyvars rhs ⊆ tyvars (type of c)`; the kernel's `term_tyvars` counts every type
annotation, including binder domains, so it is stated for `Term.annotVars` (not the weaker
`Term.typeVars`, which omits the domain of an unused binder). This is what makes a definition
step preserve locality of the constant interpretation (`DefinitionGate.withDefinition_local`). -/
structure DefinitionGate (S : Signature) where
  id : Nat
  rhs : Term S [] (S id)
  fresh : id ∉ rhs.constIds
  typeVarsClosed : rhs.annotVars ⊆ (S id).typeVars

theorem DefinitionGate.type_vars_closed (D : DefinitionGate S) :
    D.rhs.typeVars ⊆ (S D.id).typeVars :=
  fun _ hi ↦ D.typeVarsClosed (D.rhs.typeVars_subset_annotVars hi)

theorem DefinitionGate.instType_type_vars_closed
    (D : DefinitionGate S) (θ : TypeSub) :
    (D.rhs.instType θ).typeVars ⊆ ((S D.id).subst θ).typeVars := by
  intro i hi
  rw [Term.typeVars_instType] at hi
  rw [Ty.typeVars_subst]
  rcases hi with ⟨j, hj, hi⟩
  exact ⟨j, D.type_vars_closed hj, hi⟩

def DefinitionGate.head (D : DefinitionGate S) : Term S [] (S D.id) :=
  .const D.id (S D.id) (Ty.IsInst.refl _)

/-- A constant occurrence at the type `τ = S c` evaluates to the interpretation, for a local
interpretation. -/
theorem eval_const_self (I : ConstVal κ S) {c : Nat} (hI : I.Local c) {τ : Ty}
    (e : S c = τ) (h : (S c).IsInst τ) (ρ : TypeVal) (hρ : Admissible κ ρ)
    {Γ : List Ty} (η : Env κ ρ Γ) :
    HEq ((Term.const c τ h).eval I ρ hρ η) (I ρ hρ c) := by
  subst e
  refine (cast_heq _ _).trans (hI _ _ ρ hρ ?_)
  intro i hi
  have := Ty.constSub_eq (S c) (S c) h (σ := Ty.var) (Ty.subst_id _) i hi
  simp only [TypeSub.pull, this]
  rfl

noncomputable def ConstVal.withDefinition (I : ConstVal κ S) (D : DefinitionGate S) :
    ConstVal κ S := fun ρ hρ c ↦
  if h : c = D.id then h.symm ▸ D.rhs.eval I ρ hρ closedEnv
  else I ρ hρ c

noncomputable def ConstVal.override (I : ConstVal κ S) (c : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible κ ρ), (S c).denote κ ρ) : ConstVal κ S :=
  fun ρ hρ n ↦ if h : n = c then h.symm ▸ v ρ hρ else I ρ hρ n

theorem ConstVal.override_agree (I : ConstVal κ S) (c n : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible κ ρ), (S c).denote κ ρ)
    (h : n ≠ c) (ρ : TypeVal) (hρ : Admissible κ ρ) :
    I.override c v ρ hρ n = I ρ hρ n := by
  simp [ConstVal.override, h]

theorem ConstVal.override_value (I : ConstVal κ S) (c : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible κ ρ), (S c).denote κ ρ)
    (ρ : TypeVal) (hρ : Admissible κ ρ) :
    I.override c v ρ hρ c = v ρ hρ := by
  simp [ConstVal.override]

theorem DefinitionGate.rhs_eval_withDefinition (D : DefinitionGate S)
    (I : ConstVal κ S) (ρ : TypeVal) (hρ : Admissible κ ρ) :
    D.rhs.eval (I.withDefinition D) ρ hρ closedEnv =
      D.rhs.eval I ρ hρ closedEnv := by
  apply Term.eval_agree D.rhs (I.withDefinition D) I ρ hρ closedEnv
  intro c hc ρ' hρ'
  by_cases h : c = D.id
  · exact False.elim (D.fresh (by simpa [h] using hc))
  · simp [ConstVal.withDefinition, h]

/-- Rewriting a hypothesis cast along a type equality is transparent for `HEq`. -/
theorem heq_rec_symm {T : Ty → Type} {a b : Ty} (h : a = b) (x : T a) : HEq (h ▸ x) x := by
  subst h
  rfl

theorem DefinitionGate.withDefinition_agree (D : DefinitionGate S)
    (I : ConstVal κ S) {c : Nat} (hc : c ≠ D.id) :
    ∀ (ρ : TypeVal) (hρ : Admissible κ ρ),
      I.withDefinition D ρ hρ c = I ρ hρ c := by
  intro ρ hρ
  simp [ConstVal.withDefinition, hc]

/-- A definition step preserves locality of the constant interpretation: the new value of
`id` is the evaluation of a term whose annotations lie in the type variables of `S id`. -/
theorem DefinitionGate.withDefinition_local (D : DefinitionGate S) (I : ConstVal κ S)
    (hI : ∀ c, I.Local c) (c : Nat) : (I.withDefinition D).Local c := by
  intro ρ hρ ρ' hρ' hag
  by_cases h : c = D.id
  · subst h
    have e1 : I.withDefinition D ρ hρ D.id = D.rhs.eval I ρ hρ closedEnv := by
      simp [ConstVal.withDefinition]
    have e2 : I.withDefinition D ρ' hρ' D.id = D.rhs.eval I ρ' hρ' closedEnv := by
      simp [ConstVal.withDefinition]
    rw [e1, e2]
    exact Term.eval_congr_vars hρ hρ' I D.rhs (fun i hi ↦ hag i (D.typeVarsClosed hi))
      (fun c _ ↦ hI c) closedEnv closedEnv (fun _ v _ ↦ nomatch v)
  · rw [D.withDefinition_agree I h ρ hρ, D.withDefinition_agree I h ρ' hρ']
    exact hI c ρ hρ ρ' hρ' hag

/-- Old-language invariance of a definition step across a change of model. -/
theorem valid_definition_old_language_iff_κ {κ' : TyConVal}
    (D : DefinitionGate S) (I : ConstVal κ S) (J : ConstVal κ' S) (s : Sequent S Γ)
    (hOld : D.id ∉ s.constIds) (hAdm : ∀ ρ, Admissible κ ρ ↔ Admissible κ' ρ)
    (hC : κ.AgreeOn s.tyCons κ')
    (hAgree : ∀ c, c ∈ s.constIds → I.AgreeAt J s.tyCons c) :
    Valid (I.withDefinition D) s ↔ Valid J s :=
  valid_iff_κ (I.withDefinition D) J hAdm hC fun c hc ↦
    ConstVal.AgreeAt.congr_left
      (fun ρ hρ ↦ D.withDefinition_agree I (fun h ↦ hOld (h ▸ hc)) ρ hρ) (hAgree c hc)

theorem valid_definition_old_language_iff
    (D : DefinitionGate S) (I : ConstVal κ S) (s : Sequent S Γ)
    (hOld : D.id ∉ s.constIds) :
    Valid (I.withDefinition D) s ↔ Valid I s :=
  valid_definition_old_language_iff_κ D I I s hOld (fun _ ↦ Iff.rfl)
    (TyConVal.AgreeOn.refl κ _) fun _ _ ↦ ConstVal.AgreeAt.of_eq fun _ _ ↦ rfl

theorem valid_definition_equation (D : DefinitionGate S) (I : ConstVal κ S)
    (hI : ∀ c, I.Local c) :
    Valid (I.withDefinition D)
      { hyps := [], concl := (D.head.equal D.rhs) } := by
  intro ρ hρ η _
  change D.head.eval (I.withDefinition D) ρ hρ η =
    D.rhs.eval (I.withDefinition D) ρ hρ η
  have hη : η = closedEnv := by
    funext a v
    cases v
  subst η
  set π := (Ty.constSub (S D.id) (S D.id) (Ty.IsInst.refl _)).pull κ ρ with hπ
  have hπa : Admissible κ π := TypeSub.pull_admissible _ κ ρ hρ
  have hag : ∀ i, i ∈ (S D.id).typeVars → π i = ρ i := by
    intro i hi
    have := Ty.constSub_eq (S D.id) (S D.id) (Ty.IsInst.refl _) (σ := Ty.var)
      (Ty.subst_id _) i hi
    simp only [hπ, TypeSub.pull, this]
    rfl
  have h1 : HEq (D.head.eval (I.withDefinition D) ρ hρ closedEnv)
      (D.rhs.eval I π hπa closedEnv) := by
    refine (cast_heq _ _).trans ?_
    have e : I.withDefinition D π hπa D.id = D.rhs.eval I π hπa closedEnv := by
      simp [ConstVal.withDefinition, DefinitionGate.rhs_eval_withDefinition]
    rw [e]
  have h2 : HEq (D.rhs.eval I π hπa closedEnv) (D.rhs.eval I ρ hρ closedEnv) :=
    Term.eval_congr_vars hπa hρ I D.rhs (fun i hi ↦ hag i (D.typeVarsClosed hi))
      (fun c _ ↦ hI c) closedEnv closedEnv (fun _ v _ ↦ nomatch v)
  exact eq_of_heq (h1.trans (h2.trans (D.rhs_eval_withDefinition I ρ hρ ▸ HEq.rfl)))

end QEDFV.HOL
