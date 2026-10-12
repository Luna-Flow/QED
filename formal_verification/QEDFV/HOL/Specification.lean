import QEDFV.HOL.Definitions

namespace QEDFV.HOL

variable {κ : TyConVal}

def specificationTerm (p : Term S (a :: Γ) .bool) : Term S Γ a :=
  Term.choice.app (Term.lam p)

theorem valid_specification
    (I : ConstVal κ S) (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
    (hWitness : Valid I
      { hyps := [], concl := p.substitute (Sub.single w) }) :
    Valid I
      { hyps := [], concl := p.substitute (Sub.single (specificationTerm p)) } := by
  intro ρ hρ η _
  have hw := hWitness ρ hρ η (by
    intro h hh
    cases hh)
  change (p.substitute (Sub.single (specificationTerm p))).eval I ρ hρ η
  rw [Term.eval_substitute, Sub.eval_single]
  rw [Term.eval_substitute] at hw
  rw [Sub.eval_single] at hw
  letI : Nonempty (Ty.denote κ ρ a) := a.carrier_nonempty κ ρ hρ
  change p.eval I ρ hρ
    (Env.extend η ((Term.choice.app (Term.lam p)).eval I ρ hρ η))
  change p.eval I ρ hρ
    (Env.extend η
      ((select (Ty.denote κ ρ a))
        (fun q ↦ p.eval I ρ hρ (Env.extend η q))))
  exact select_spec (Ty.denote κ ρ a)
    (fun q ↦ p.eval I ρ hρ (Env.extend η q))
    ⟨w.eval I ρ hρ η, hw⟩

/-- The gate of a constant specification. As for `DefinitionGate`, `typeVarsClosed` is stated
for `Term.annotVars`, matching the kernel's `term_tyvars` (binder domains included). -/
structure SpecificationGate (S : Signature) where
  id : Nat
  ty : Ty
  predicate : Term S (ty :: []) .bool
  witness : Term S [] ty
  fresh : id ∉ predicate.constIds ∪ witness.constIds
  typeVarsClosed : predicate.annotVars ⊆ ty.typeVars

theorem SpecificationGate.type_vars_closed (G : SpecificationGate S) :
    G.predicate.typeVars ⊆ G.ty.typeVars :=
  fun _ hi ↦ G.typeVarsClosed (G.predicate.typeVars_subset_annotVars hi)

theorem SpecificationGate.instType_type_vars_closed
    (G : SpecificationGate S) (θ : TypeSub) :
    (G.predicate.instType θ).typeVars ⊆ (G.ty.subst θ).typeVars := by
  intro i hi
  rw [Term.typeVars_instType] at hi
  rw [Ty.typeVars_subst]
  rcases hi with ⟨j, hj, hi⟩
  exact ⟨j, G.type_vars_closed hj, hi⟩

def SpecificationGate.body (G : SpecificationGate S) : Term S [] .bool :=
  G.predicate.substitute (Sub.single G.witness)

def SpecificationGate.constant (G : SpecificationGate S)
    (hTy : S G.id = G.ty) : Term S [] G.ty :=
  let hEq : Ty.subst Ty.var (S G.id) = G.ty :=
    (Ty.subst_id (S G.id)).trans hTy
  hEq ▸ (Term.const (S := S) G.id Ty.var)

noncomputable def ConstVal.withSpecification (I : ConstVal κ S)
    (G : SpecificationGate S) (hTy : S G.id = G.ty) : ConstVal κ S :=
  I.override G.id (fun ρ hρ ↦
    hTy.symm ▸ (specificationTerm G.predicate).eval I ρ hρ closedEnv)

theorem SpecificationGate.constant_eval_withSpecification
    (G : SpecificationGate S) (I : ConstVal κ S) (hTy : S G.id = G.ty)
    (ρ : TypeVal) (hρ : Admissible κ ρ) :
    (G.constant hTy).eval (I.withSpecification G hTy) ρ hρ closedEnv =
      (specificationTerm G.predicate).eval I ρ hρ closedEnv := by
  let hEq : Ty.subst Ty.var (S G.id) = G.ty :=
    (Ty.subst_id (S G.id)).trans hTy
  have hcast := eval_term_cast (I.withSpecification G hTy) ρ hρ closedEnv
    hEq (.const G.id Ty.var)
  have hraw := eval_const_var (I.withSpecification G hTy) ρ hρ G.id closedEnv
  have hoverride := ConstVal.override_value I G.id
    (fun ρ hρ ↦ hTy.symm ▸ (specificationTerm G.predicate).eval I ρ hρ closedEnv)
    ρ hρ
  have hvalue : HEq
      ((Term.const G.id Ty.var).eval (I.withSpecification G hTy) ρ hρ closedEnv)
      (hTy.symm ▸ (specificationTerm G.predicate).eval I ρ hρ closedEnv) := by
    exact hraw.trans (by exact heq_of_eq hoverride)
  simpa [SpecificationGate.constant, hEq] using hcast.trans hvalue

/-- A specification step preserves locality of the constant interpretation. -/
theorem SpecificationGate.withSpecification_local (G : SpecificationGate S) (I : ConstVal κ S)
    (hTy : S G.id = G.ty) (hI : ∀ c, I.Local c) (c : Nat) :
    (I.withSpecification G hTy).Local c := by
  intro ρ hρ ρ' hρ' hag
  by_cases h : c = G.id
  · subst h
    have e1 : I.withSpecification G hTy ρ hρ G.id =
        hTy.symm ▸ (specificationTerm G.predicate).eval I ρ hρ closedEnv := by
      simp [ConstVal.withSpecification, ConstVal.override]
    have e2 : I.withSpecification G hTy ρ' hρ' G.id =
        hTy.symm ▸ (specificationTerm G.predicate).eval I ρ' hρ' closedEnv := by
      simp [ConstVal.withSpecification, ConstVal.override]
    rw [e1, e2]
    refine (heq_rec_symm (T := fun t ↦ t.denote κ ρ) hTy.symm _).trans
      (HEq.trans ?_ (heq_rec_symm (T := fun t ↦ t.denote κ ρ') hTy.symm _).symm)
    refine Term.eval_congr_vars hρ hρ' I (specificationTerm G.predicate) ?_
      (fun c _ ↦ hI c) closedEnv closedEnv (fun _ v _ ↦ nomatch v)
    intro i hi
    have hty : ∀ i, i ∈ G.ty.typeVars → ρ i = ρ' i := fun i hi ↦ hag i (hTy ▸ hi)
    have hi' : i ∈ G.ty.typeVars ∨ i ∈ G.predicate.annotVars := by
      simpa [specificationTerm, Term.annotVars, Ty.typeVars] using hi
    rcases hi' with h | h
    · exact hty i h
    · exact hty i (G.typeVarsClosed h)
  · have a1 : I.withSpecification G hTy ρ hρ c = I ρ hρ c :=
      ConstVal.override_agree I G.id c _ h ρ hρ
    have a2 : I.withSpecification G hTy ρ' hρ' c = I ρ' hρ' c :=
      ConstVal.override_agree I G.id c _ h ρ' hρ'
    rw [a1, a2]
    exact hI c ρ hρ ρ' hρ' hag

theorem SpecificationGate.valid_body (G : SpecificationGate S) (I : ConstVal κ S)
    (hWitness : Valid I { hyps := [], concl := G.body }) :
    Valid I
      { hyps := [], concl := G.predicate.substitute
          (Sub.single (specificationTerm G.predicate)) } :=
  valid_specification I G.predicate G.witness hWitness

theorem SpecificationGate.valid_constant (G : SpecificationGate S) (I : ConstVal κ S)
    (hTy : S G.id = G.ty)
    (hWitness : Valid I { hyps := [], concl := G.body }) :
    Valid (I.withSpecification G hTy)
      { hyps := [], concl := G.predicate.substitute (Sub.single (G.constant hTy)) } := by
  intro ρ hρ η _
  have hη : η = closedEnv := by
    funext a v
    cases v
  subst η
  have hSpec := valid_specification I G.predicate G.witness hWitness ρ hρ closedEnv (by
    intro h hh
    cases hh)
  change (G.predicate.substitute (Sub.single (G.constant hTy))).eval
    (I.withSpecification G hTy) ρ hρ closedEnv
  rw [Term.eval_substitute, Sub.eval_single]
  rw [Term.eval_substitute] at hSpec
  rw [Sub.eval_single] at hSpec
  have hConst := G.constant_eval_withSpecification I hTy ρ hρ
  change G.predicate.eval (I.withSpecification G hTy) ρ hρ
    (Env.extend closedEnv
      ((G.constant hTy).eval (I.withSpecification G hTy) ρ hρ closedEnv))
  rw [hConst]
  have hPred := Term.eval_agree G.predicate (I.withSpecification G hTy) I ρ hρ
      (Env.extend closedEnv
        ((specificationTerm G.predicate).eval I ρ hρ closedEnv)) (by
    intro c hc ρ' hρ'
    exact ConstVal.override_agree I G.id c
      (fun ρ hρ ↦ hTy.symm ▸
        (specificationTerm G.predicate).eval I ρ hρ closedEnv)
      (fun h ↦ G.fresh (Finset.mem_union_left _ (by simpa [h] using hc))) ρ' hρ')
  rw [hPred]
  exact hSpec

theorem SpecificationGate.valid_old_language_iff
    (G : SpecificationGate S) (I : ConstVal κ S) (hTy : S G.id = G.ty)
    (s : Sequent S Γ) (hOld : G.id ∉ s.constIds) :
    Valid (I.withSpecification G hTy) s ↔ Valid I s := by
  constructor
  · intro hValid
    apply valid_transport (I.withSpecification G hTy) I
    · intro c hc ρ hρ
      simpa [ConstVal.withSpecification] using (ConstVal.override_agree I G.id c
        (fun ρ hρ ↦ hTy.symm ▸
          (specificationTerm G.predicate).eval I ρ hρ closedEnv)
        (fun h ↦ hOld (h ▸ hc)) ρ hρ)
    · exact hValid
  · intro hValid
    apply valid_transport I (I.withSpecification G hTy)
    · intro c hc ρ hρ
      simpa [ConstVal.withSpecification] using (ConstVal.override_agree I G.id c
        (fun ρ hρ ↦ hTy.symm ▸
          (specificationTerm G.predicate).eval I ρ hρ closedEnv)
        (fun h ↦ hOld (h ▸ hc)) ρ hρ).symm
    · exact hValid

theorem SpecificationGate.valid_constant_from_derivation
    (hChoice : ChoiceNatural) (G : SpecificationGate S) (I : ConstVal κ S)
    (hTy : S G.id = G.ty)
    (d : Derivation S { hyps := [], concl := G.body }) :
    Valid (I.withSpecification G hTy)
      { hyps := [], concl := G.predicate.substitute (Sub.single (G.constant hTy)) } :=
  G.valid_constant I hTy (derivation_sound hChoice I d)

theorem specification_valid_from_derivation
    (hChoice : ChoiceNatural) (I : ConstVal κ S)
    (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
    (d : Derivation S
      { hyps := [], concl := p.substitute (Sub.single w) }) :
    Valid I
      { hyps := [], concl := p.substitute (Sub.single (specificationTerm p)) } :=
  valid_specification I p w (derivation_sound hChoice I d)

theorem SpecificationGate.valid_constant_from_typed_derivation
    (G : SpecificationGate S) (I : ConstVal κ S)
    (hTy : S G.id = G.ty)
    (d : Derivation S { hyps := [], concl := G.body }) :
    Valid (I.withSpecification G hTy)
      { hyps := [], concl := G.predicate.substitute (Sub.single (G.constant hTy)) } :=
  G.valid_constant I hTy (derivation_sound select_natural I d)

theorem specification_valid_from_typed_derivation
    (I : ConstVal κ S)
    (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
    (d : Derivation S
      { hyps := [], concl := p.substitute (Sub.single w) }) :
    Valid I
      { hyps := [], concl := p.substitute (Sub.single (specificationTerm p)) } :=
  valid_specification I p w (derivation_sound select_natural I d)

end QEDFV.HOL
