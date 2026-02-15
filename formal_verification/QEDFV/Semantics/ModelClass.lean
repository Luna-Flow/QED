import QEDFV.Semantics.Model

namespace QEDFV

structure AdmissibleModelClass (t : TheoryState) where
  model : Model
  lawBundle : ModelLawBundle model
  choiceCompatible : Prop
  infinityAnchor : Prop
  gateAdmitted : Prop
  eqToFalseElim :
    ∀ e : DbExpr,
      model.ValidExpr (mkEqExpr e (Lean.Expr.const `False [])) ->
      ¬ model.ValidExpr e
  soundKernel :
    ∀ {k : KernelState} {s : Sequent},
      k.T = t ->
      Derivable k s ->
      Valid model s

theorem modelclass_inst_type_preserves_valid
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hState : k.T = t)
    (hSubst : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : def_inst_coherent theta s)
    (hConst : const_instance_ok theta s)
    (hStruct : theorem_structure_preserved theta s)
    (hValid : Valid mc.model s) :
    Valid mc.model (applyTypeSubstSequent theta s) := by
  subst hState
  exact bundle_inst_type_capsule
    mc.model mc.lawBundle k theta s hSubst hImg hTyping hDef hConst hStruct hValid

theorem modelclass_inst_term_preserves_valid
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (sigma : TermSubst)
    (s : Sequent)
    (hSubst : valid_term_subst sigma)
    (hValid : Valid mc.model s) :
    Valid mc.model (applyTermSubstSequent sigma s) := by
  exact bundle_inst_term_capsule mc.model mc.lawBundle sigma s hSubst hValid

theorem modelclass_alpha_respect
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    {e1 e2 : DbExpr}
    (hAlpha : AlphaEqExpr e1 e2)
    (hValid : mc.model.ValidExpr e1) :
    mc.model.ValidExpr e2 := by
  exact bundle_alpha_capsule mc.model mc.lawBundle hAlpha hValid

def modelClassNonempty (t : TheoryState) : Prop :=
  Nonempty (AdmissibleModelClass t)

theorem semantic_non_triviality_transfer
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (k : KernelState)
    (s : Sequent)
    (hState : k.T = t)
    (hNotValid : ¬ Valid mc.model s) :
    ¬ Derivable k s := by
  intro hDerivable
  exact hNotValid (mc.soundKernel hState hDerivable)

theorem consistency_witness_form
    (t : TheoryState)
    (hNonempty : modelClassNonempty t)
    (k : KernelState)
    (s : Sequent)
    (hState : k.T = t)
    (hClosed : s.hyps = [])
    (hDerivable : Derivable k s)
    (hNegDerivable : Derivable k { hyps := s.hyps, concl := mkEqExpr s.concl (Lean.Expr.const `False []) }) :
    False := by
  rcases hNonempty with ⟨mc⟩
  have hValid : Valid mc.model s := mc.soundKernel hState hDerivable
  have hNegValid : Valid mc.model { hyps := s.hyps, concl := mkEqExpr s.concl (Lean.Expr.const `False []) } :=
    mc.soundKernel hState hNegDerivable
  have hConcl : mc.model.ValidExpr s.concl := by
    refine hValid ?_
    intro h hmem
    rw [hClosed] at hmem
    cases hmem
  have hEqFalse : mc.model.ValidExpr (mkEqExpr s.concl (Lean.Expr.const `False [])) := by
    refine hNegValid ?_
    intro h hmem
    rw [hClosed] at hmem
    cases hmem
  exact (mc.eqToFalseElim s.concl hEqFalse) hConcl

end QEDFV
