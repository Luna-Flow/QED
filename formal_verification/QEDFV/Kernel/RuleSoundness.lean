import QEDFV.Semantics.Model

namespace QEDFV

def primitive_sound_REFL : Prop :=
  forall (m : Model) (_k : KernelState) (t : DbExpr),
    Valid m { hyps := [], concl := mkEqExpr t t }

def primitive_sound_ASSUME : Prop :=
  forall (m : Model) (_k : KernelState) (p : DbExpr),
    IsBoolExpr p ->
    alphaMember p [p] ->
    Valid m { hyps := [p], concl := p }

def primitive_sound_TRANS : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent) (x y y' z : DbExpr),
    ModelAlphaLaws m ->
    A.concl = mkEqExpr x y ->
    B.concl = mkEqExpr y' z ->
    AlphaEqExpr y y' ->
    Valid m A ->
    Valid m B ->
    Valid m { hyps := alphaUnion A.hyps B.hyps, concl := mkEqExpr x z }

def primitive_sound_MK_COMB : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent) (f g x y : DbExpr),
    A.concl = mkEqExpr f g ->
    B.concl = mkEqExpr x y ->
    Valid m A ->
    Valid m B ->
    Valid m { hyps := alphaUnion A.hyps B.hyps, concl := mkCombEqExpr f g x y }

def primitive_sound_ABS : Prop :=
  forall (m : Model) (_k : KernelState) (A : Sequent) (n : Lean.Name) (ty s t : DbExpr),
    A.concl = mkEqExpr s t ->
    (∀ h, h ∈ A.hyps -> ¬ dbHasLooseBVar h 0) ->
    Valid m A ->
    Valid m { hyps := A.hyps, concl := mkAbsEqExpr n ty s t }

def primitive_sound_BETA : Prop :=
  forall (m : Model) (_k : KernelState) (r : TypedBetaRedex),
    betaBinderAgreement r ->
    Valid m { hyps := [], concl := mkEqExpr (betaRedexExpr r) (typedBetaContract r) }

def primitive_sound_EQ_MP : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent) (p q p' : DbExpr),
    ModelAlphaLaws m ->
    A.concl = mkEqExpr p q ->
    AlphaEqExpr p p' ->
    B.concl = p' ->
    IsBoolExpr p ->
    Valid m A ->
    Valid m B ->
    Valid m { hyps := alphaUnion A.hyps B.hyps, concl := q }

def primitive_sound_DEDUCT_ANTISYM_RULE : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent),
    ModelAlphaLaws m ->
    alphaAssumptionEq
      (alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl))
      (alphaUnion A.hyps B.hyps) ->
    Valid m A ->
    Valid m B ->
    Valid m
      { hyps := alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl)
      , concl := mkEqExpr A.concl B.concl
      }

def primitive_sound_INST_TYPE : Prop :=
  forall (m : Model) (k : KernelState) (theta : TypeSubst) (A : Sequent),
    ModelSubstLaws m ->
    valid_ty_subst theta ->
    admissible_ty_image k.T theta ->
    typing_preserved_under_ty_subst theta A ->
    def_inst_coherent theta A ->
    const_instance_ok theta A ->
    theorem_structure_preserved theta A ->
    Valid m A ->
    Valid m (applyTypeSubstSequent theta A)

def primitive_sound_INST : Prop :=
  forall (m : Model) (_k : KernelState) (sigma : TermSubst) (A : Sequent),
    ModelSubstLaws m ->
    valid_term_subst sigma ->
    Valid m A ->
    Valid m (applyTermSubstSequent sigma A)

def primitive_sound_all : Prop :=
  primitive_sound_REFL ∧
  primitive_sound_ASSUME ∧
  primitive_sound_TRANS ∧
  primitive_sound_MK_COMB ∧
  primitive_sound_ABS ∧
  primitive_sound_BETA ∧
  primitive_sound_EQ_MP ∧
  primitive_sound_DEDUCT_ANTISYM_RULE ∧
  primitive_sound_INST_TYPE ∧
  primitive_sound_INST

theorem primitive_sound_REFL_proved : primitive_sound_REFL := by
  intro m k t hHyps
  exact m.validEqRefl t

theorem primitive_sound_ASSUME_proved : primitive_sound_ASSUME := by
  intro m k p _ _ hHyps
  exact hHyps p (by simp)

theorem primitive_sound_TRANS_proved : primitive_sound_TRANS := by
  intro m k A B x y y' z hAlphaLaws hEqA hEqB hMid hA hB hHyps
  have hAConcl : m.ValidExpr A.concl := by
    refine hA ?_
    intro h hh
    exact hHyps h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_left B.hyps hh))
  have hBConcl : m.ValidExpr B.concl := by
    refine hB ?_
    intro h hh
    exact hHyps h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_right A.hyps hh))
  have hEqXY : m.ValidExpr (mkEqExpr x y) := by
    simpa [hEqA] using hAConcl
  have hEqY'Z : m.ValidExpr (mkEqExpr y' z) := by
    simpa [hEqB] using hBConcl
  have hEqYZ : m.ValidExpr (mkEqExpr y z) := by
    exact hAlphaLaws.alphaRespect (alphaEq_symm (alphaEq_mkEqExpr_left hMid)) hEqY'Z
  exact m.validEqTrans x y z hEqXY hEqYZ

theorem primitive_sound_MK_COMB_proved : primitive_sound_MK_COMB := by
  intro m k A B f g x y hEqA hEqB hA hB hHyps
  have hAConcl : m.ValidExpr A.concl := by
    refine hA ?_
    intro h hh
    exact hHyps h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_left B.hyps hh))
  have hBConcl : m.ValidExpr B.concl := by
    refine hB ?_
    intro h hh
    exact hHyps h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_right A.hyps hh))
  have hEqFG : m.ValidExpr (mkEqExpr f g) := by
    simpa [hEqA] using hAConcl
  have hEqXY : m.ValidExpr (mkEqExpr x y) := by
    simpa [hEqB] using hBConcl
  exact m.validEqCongrApp f g x y hEqFG hEqXY

theorem primitive_sound_ABS_proved : primitive_sound_ABS := by
  intro m k A n ty s t hEq hNoLoose hA hHyps
  have hEqST : m.ValidExpr (mkEqExpr s t) := by
    have hAConcl : m.ValidExpr A.concl := by
      refine hA ?_
      intro h hh
      exact hHyps h (by simpa [hEq] using hh)
    simpa [hEq] using hAConcl
  exact m.validEqCongrLam n ty s t hEqST

theorem primitive_sound_BETA_proved : primitive_sound_BETA := by
  intro m k r hAgree hHyps
  exact m.validBeta r hAgree

theorem primitive_sound_EQ_MP_proved : primitive_sound_EQ_MP := by
  intro m k A B p q p' hAlphaLaws hEq hAlpha hPrem _hBool hA hB hHyps
  have hAConcl : m.ValidExpr A.concl := by
    refine hA ?_
    intro h hh
    exact hHyps h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_left B.hyps hh))
  have hEqConcl : m.ValidExpr (mkEqExpr p q) := by
    simpa [hEq] using hAConcl
  have hPremConcl' : m.ValidExpr p' := by
    have hBConcl : m.ValidExpr B.concl := by
      refine hB ?_
      intro h hh
      exact hHyps h (by
        simpa [alphaUnion, hypsUnion] using (List.mem_append_right A.hyps hh))
    simpa [hPrem] using hBConcl
  have hPremConcl : m.ValidExpr p := by
    exact hAlphaLaws.alphaRespect (alphaEq_symm hAlpha) hPremConcl'
  exact m.validEqMp p q hEqConcl hPremConcl

theorem primitive_sound_DEDUCT_ANTISYM_RULE_proved : primitive_sound_DEDUCT_ANTISYM_RULE := by
  intro m k A B hAlphaLaws hAlpha hA hB hHyps
  let remHyps := alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl)
  have hUnion : ∀ h, h ∈ alphaUnion A.hyps B.hyps -> m.ValidExpr h := by
    intro h hhUnion
    have hMemUnion : alphaMember h (alphaUnion A.hyps B.hyps) := ⟨h, hhUnion, alphaEq_refl h⟩
    have hMemRem : memAlpha h remHyps := (hAlpha h).2 hMemUnion
    rcases hMemRem with ⟨h', hhRem, hAlphaHH'⟩
    have hValid' : m.ValidExpr h' := hHyps h' hhRem
    exact hAlphaLaws.alphaRespect (alphaEq_symm hAlphaHH') hValid'
  have hAConcl : m.ValidExpr A.concl := by
    refine hA ?_
    intro h hh
    exact hUnion h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_left B.hyps hh))
  have hBConcl : m.ValidExpr B.concl := by
    refine hB ?_
    intro h hh
    exact hUnion h (by
      simpa [alphaUnion, hypsUnion] using (List.mem_append_right A.hyps hh))
  exact m.validEqIntro A.concl B.concl hAConcl hBConcl

theorem primitive_sound_INST_TYPE_proved : primitive_sound_INST_TYPE := by
  intro m k theta A hLaws hSubst hImg hTyping hDef hConst hStruct hA
  have hPrem : InstTypePremises k theta A := by
    exact ⟨hSubst, hImg, hTyping, hDef, hConst, hStruct⟩
  have hNoFailure : instTypeFailure k theta A = none :=
    instTypeFailure_none_of_premises k theta A hPrem
  have _ : instTypeFailure k theta A = none := hNoFailure
  exact hLaws.typeSubstPreservesValid k theta A hSubst hImg hTyping hDef hConst hStruct hA

theorem primitive_sound_INST_proved : primitive_sound_INST := by
  intro m k sigma A hLaws hSubst hA
  exact hLaws.termSubstPreservesValid sigma A hSubst hA

theorem primitive_sound_all_proved : primitive_sound_all := by
  exact ⟨
    primitive_sound_REFL_proved,
    primitive_sound_ASSUME_proved,
    primitive_sound_TRANS_proved,
    primitive_sound_MK_COMB_proved,
    primitive_sound_ABS_proved,
    primitive_sound_BETA_proved,
    primitive_sound_EQ_MP_proved,
    primitive_sound_DEDUCT_ANTISYM_RULE_proved,
    primitive_sound_INST_TYPE_proved,
    primitive_sound_INST_proved
  ⟩

end QEDFV
