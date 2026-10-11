import QEDFV.HOL.Transport

namespace QEDFV.HOL

def closedEnv {ρ : TypeVal} : Env ρ [] := fun _ v ↦ by cases v

structure DefinitionGate (S : Signature) where
  id : Nat
  rhs : Term S [] (S id)
  fresh : id ∉ rhs.constIds

def DefinitionGate.head (D : DefinitionGate S) : Term S [] (S D.id) :=
  (Ty.subst_id (S D.id)).symm ▸ (.const D.id Ty.var)

theorem eval_const_var (I : ConstVal S) (ρ : TypeVal) (hρ : Admissible ρ)
    (c : Nat) (η : Env ρ Γ) :
    HEq ((Term.const c Ty.var).eval I ρ hρ η) (I ρ hρ c) := by
  change HEq
    (cast (Ty.denote_subst (S c) Ty.var ρ).symm
      (I (TypeSub.pull Ty.var ρ) (TypeSub.pull_admissible Ty.var ρ hρ) c))
    (I ρ hρ c)
  have hI := constVal_heq I (show TypeSub.pull Ty.var ρ = ρ by rfl)
    (TypeSub.pull_admissible Ty.var ρ hρ) hρ c
  exact (cast_heq _ _).trans hI

noncomputable def ConstVal.withDefinition (I : ConstVal S) (D : DefinitionGate S) :
    ConstVal S := fun ρ hρ c ↦
  if h : c = D.id then h.symm ▸ D.rhs.eval I ρ hρ closedEnv
  else I ρ hρ c

noncomputable def ConstVal.override (I : ConstVal S) (c : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible ρ), (S c).denote ρ) : ConstVal S :=
  fun ρ hρ n ↦ if h : n = c then h.symm ▸ v ρ hρ else I ρ hρ n

theorem ConstVal.override_agree (I : ConstVal S) (c n : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible ρ), (S c).denote ρ)
    (h : n ≠ c) (ρ : TypeVal) (hρ : Admissible ρ) :
    I.override c v ρ hρ n = I ρ hρ n := by
  simp [ConstVal.override, h]

theorem ConstVal.override_value (I : ConstVal S) (c : Nat)
    (v : ∀ (ρ : TypeVal) (_hρ : Admissible ρ), (S c).denote ρ)
    (ρ : TypeVal) (hρ : Admissible ρ) :
    I.override c v ρ hρ c = v ρ hρ := by
  simp [ConstVal.override]

theorem DefinitionGate.rhs_eval_withDefinition (D : DefinitionGate S)
    (I : ConstVal S) (ρ : TypeVal) (hρ : Admissible ρ) :
    D.rhs.eval (I.withDefinition D) ρ hρ closedEnv =
      D.rhs.eval I ρ hρ closedEnv := by
  apply Term.eval_agree D.rhs (I.withDefinition D) I ρ hρ closedEnv
  intro c hc ρ' hρ'
  by_cases h : c = D.id
  · exact False.elim (D.fresh (by simpa [h] using hc))
  · simp [ConstVal.withDefinition, h]

theorem DefinitionGate.withDefinition_agree (D : DefinitionGate S)
    (I : ConstVal S) {c : Nat} (hc : c ≠ D.id) :
    ∀ (ρ : TypeVal) (hρ : Admissible ρ),
      I.withDefinition D ρ hρ c = I ρ hρ c := by
  intro ρ hρ
  simp [ConstVal.withDefinition, hc]

theorem valid_definition_old_language_iff
    (D : DefinitionGate S) (I : ConstVal S) (s : Sequent S Γ)
    (hOld : D.id ∉ s.constIds) :
    Valid (I.withDefinition D) s ↔ Valid I s := by
  constructor
  · intro hValid
    apply valid_transport (I.withDefinition D) I
    · intro c hc ρ hρ
      exact D.withDefinition_agree I (fun h ↦ hOld (h ▸ hc)) ρ hρ
    · exact hValid
  · intro hValid
    apply valid_transport I (I.withDefinition D)
    · intro c hc ρ hρ
      exact (D.withDefinition_agree I (fun h ↦ hOld (h ▸ hc)) ρ hρ).symm
    · exact hValid

theorem valid_definition_equation (D : DefinitionGate S) (I : ConstVal S) :
    Valid (I.withDefinition D)
      { hyps := [], concl := (D.head.equal D.rhs) } := by
  intro ρ hρ η _
  change D.head.eval (I.withDefinition D) ρ hρ η =
    D.rhs.eval (I.withDefinition D) ρ hρ η
  have hη : η = closedEnv := by
    funext a v
    cases v
  subst η
  have hhead : D.head.eval (I.withDefinition D) ρ hρ closedEnv =
      D.rhs.eval I ρ hρ closedEnv := by
    have hcast := eval_term_cast (I.withDefinition D) ρ hρ closedEnv
      (Ty.subst_id (S D.id)) (.const D.id Ty.var)
    have hdenote := congrArg (Ty.denote ρ) (Ty.subst_id (S D.id))
    have htarget : HEq
        (D.head.eval (I.withDefinition D) ρ hρ closedEnv)
        (cast hdenote ((Term.const (S := S) D.id Ty.var).eval
          (I.withDefinition D) ρ hρ closedEnv)) := by
      exact hcast.trans (cast_heq hdenote _).symm
    have heq := eq_of_heq htarget
    calc
      D.head.eval (I.withDefinition D) ρ hρ closedEnv =
          cast hdenote ((Term.const (S := S) D.id Ty.var).eval
            (I.withDefinition D) ρ hρ closedEnv) := heq
      _ = D.rhs.eval I ρ hρ closedEnv := by
        have hvar := eval_const_var (I.withDefinition D) ρ hρ D.id closedEnv
        have hval : HEq
            ((Term.const (S := S) D.id Ty.var).eval
              (I.withDefinition D) ρ hρ closedEnv)
            (D.rhs.eval I ρ hρ closedEnv) := by
          exact hvar.trans (by
            simp [ConstVal.withDefinition])
        have hcastval := cast_heq hdenote
          ((Term.const (S := S) D.id Ty.var).eval
            (I.withDefinition D) ρ hρ closedEnv)
        exact eq_of_heq (hcastval.trans hval)
  have hrhs := D.rhs_eval_withDefinition I ρ hρ
  exact hhead.trans hrhs.symm

end QEDFV.HOL
