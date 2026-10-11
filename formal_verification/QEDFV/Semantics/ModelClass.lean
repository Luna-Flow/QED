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

private theorem valid_of_hyps_union_left
    (m : Model)
    (A B : Sequent)
    (hA : Valid m A)
    (hHyps : ∀ h, h ∈ alphaUnion A.hyps B.hyps -> m.ValidExpr h) :
    m.ValidExpr A.concl := by
  apply hA
  intro h hh
  apply hHyps h
  exact List.mem_append_left B.hyps hh

private theorem valid_of_hyps_union_right
    (m : Model)
    (A B : Sequent)
    (hB : Valid m B)
    (hHyps : ∀ h, h ∈ alphaUnion A.hyps B.hyps -> m.ValidExpr h) :
    m.ValidExpr B.concl := by
  apply hB
  intro h hh
  apply hHyps h
  exact List.mem_append_right A.hyps hh

theorem derivable_sound
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (k : KernelState)
    (hState : k.T = t) :
    ∀ {s : Sequent}, Derivable k s -> Valid mc.model s := by
  cases hState
  intro s hDerivable
  induction hDerivable with
  | refl t =>
      intro _hHyps
      exact mc.model.validEqRefl t
  | assume p hBool hMember =>
      intro hHyps
      apply hHyps p
      simp
  | @trans A B x y y' z hEqA hEqB hMid hA hB ihA ihB =>
      intro hHyps
      have hAConcl : mc.model.ValidExpr A.concl :=
        valid_of_hyps_union_left mc.model A B ihA hHyps
      have hBConcl : mc.model.ValidExpr B.concl :=
        valid_of_hyps_union_right mc.model A B ihB hHyps
      have hEqXY : mc.model.ValidExpr (mkEqExpr x y) := by simpa [hEqA] using hAConcl
      have hEqY'Z : mc.model.ValidExpr (mkEqExpr y' z) := by simpa [hEqB] using hBConcl
      have hMidAlpha : AlphaEqExpr y y' := transMiddleTypedCoreGuard_alpha hMid
      have hEqYZ : mc.model.ValidExpr (mkEqExpr y z) :=
        mc.lawBundle.alpha.alphaRespect
          (alphaEq_symm (alphaEq_mkEqExpr_left hMidAlpha)) hEqY'Z
      exact mc.model.validEqTrans x y z hEqXY hEqYZ
  | @mkComb A B f g x y hEqA hEqB hA hB ihA ihB =>
      intro hHyps
      have hAConcl : mc.model.ValidExpr A.concl :=
        valid_of_hyps_union_left mc.model A B ihA hHyps
      have hBConcl : mc.model.ValidExpr B.concl :=
        valid_of_hyps_union_right mc.model A B ihB hHyps
      have hEqFG : mc.model.ValidExpr (mkEqExpr f g) := by simpa [hEqA] using hAConcl
      have hEqXY : mc.model.ValidExpr (mkEqExpr x y) := by simpa [hEqB] using hBConcl
      exact mc.model.validEqCongrApp f g x y hEqFG hEqXY
  | @abs A n ty s t hEq hNoLoose hA ihA =>
      intro hHyps
      have hAConcl : mc.model.ValidExpr A.concl := by
        apply ihA
        intro h hh
        exact hHyps h (by simpa [hEq] using hh)
      have hEqST : mc.model.ValidExpr (mkEqExpr s t) := by simpa [hEq] using hAConcl
      exact mc.model.validEqCongrLam n ty s t hEqST
  | beta r hGuard =>
      intro _hHyps
      exact mc.model.validBeta r hGuard.1
  | @eqMp A B p q p' hEq hAlpha hPrem hBool hA hB ihA ihB =>
      intro hHyps
      have hAConcl : mc.model.ValidExpr A.concl :=
        valid_of_hyps_union_left mc.model A B ihA hHyps
      have hBConcl : mc.model.ValidExpr B.concl :=
        valid_of_hyps_union_right mc.model A B ihB hHyps
      have hEqPQ : mc.model.ValidExpr (mkEqExpr p q) := by simpa [hEq] using hAConcl
      have hP' : mc.model.ValidExpr p' := by simpa [hPrem] using hBConcl
      have hP : mc.model.ValidExpr p :=
        mc.lawBundle.alpha.alphaRespect (alphaEq_symm hAlpha) hP'
      exact mc.model.validEqMp p q hEqPQ hP
  | @deductAntisym A B hAlpha hA hB ihA ihB =>
      intro hHyps
      have hUnion : ∀ h, h ∈ alphaUnion A.hyps B.hyps -> mc.model.ValidExpr h := by
        intro h hhUnion
        have hMemUnion : alphaMember h (alphaUnion A.hyps B.hyps) :=
          ⟨h, hhUnion, alphaEq_refl h⟩
        let remHyps := alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl)
        have hMemRem : memAlpha h remHyps := (hAlpha h).2 hMemUnion
        rcases hMemRem with ⟨h', hhRem, hAlphaHH'⟩
        exact mc.lawBundle.alpha.alphaRespect (alphaEq_symm hAlphaHH') (hHyps h' hhRem)
      have hAConcl : mc.model.ValidExpr A.concl := by
        apply ihA
        intro h hh
        exact hUnion h (List.mem_append_left B.hyps hh)
      have hBConcl : mc.model.ValidExpr B.concl := by
        apply ihB
        intro h hh
        exact hUnion h (List.mem_append_right A.hyps hh)
      exact mc.model.validEqIntro A.concl B.concl hAConcl hBConcl
  | @instType theta A hSubst hImg hObj hTyping hDef hConst hStruct hA ihA =>
      intro hHyps
      have hValid : Valid mc.model A := ihA
      have hSubstValid := mc.lawBundle.subst.typeSubstPreservesValid
        k theta A hSubst hImg hObj hTyping hDef hConst hStruct hValid
      exact hSubstValid hHyps
  | @inst sigma A hSubst hObj hA ihA =>
      intro hHyps
      have hSubstValid := mc.lawBundle.subst.termSubstPreservesValid sigma A hSubst hObj ihA
      exact hSubstValid hHyps

theorem modelclass_inst_type_preserves_valid
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hState : k.T = t)
    (hSubst : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hObj : typeSubstObjectLevelSequent theta s)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : def_inst_coherent theta s)
    (hConst : const_instance_ok theta s)
    (hStruct : theorem_structure_preserved theta s)
    (hValid : Valid mc.model s) :
    Valid mc.model (applyTypeSubstSequent theta s) := by
  subst hState
  exact bundle_inst_type_capsule
    mc.model mc.lawBundle k theta s hSubst hImg hObj hTyping hDef hConst hStruct hValid

theorem modelclass_inst_term_preserves_valid
    (t : TheoryState)
    (mc : AdmissibleModelClass t)
    (sigma : TermSubst)
    (s : Sequent)
    (hSubst : valid_term_subst sigma)
    (hObj : termSubstObjectLevelSequent sigma s)
    (hValid : Valid mc.model s) :
    Valid mc.model (applyTermSubstSequent sigma s) := by
  exact bundle_inst_term_capsule mc.model mc.lawBundle sigma s hSubst hObj hValid

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
  exact hNotValid (derivable_sound t mc k hState hDerivable)

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
  have hValid : Valid mc.model s := derivable_sound t mc k hState hDerivable
  have hNegValid : Valid mc.model { hyps := s.hyps, concl := mkEqExpr s.concl (Lean.Expr.const `False []) } :=
    derivable_sound t mc k hState hNegDerivable
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
