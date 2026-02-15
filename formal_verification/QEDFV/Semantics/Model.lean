import QEDFV.Kernel.PrimitiveRules

namespace QEDFV

structure Model where
  ValidExpr : DbExpr -> Prop
  validEqRefl : ∀ t : DbExpr, ValidExpr (mkEqExpr t t)
  validEqIntro : ∀ p q : DbExpr, ValidExpr p -> ValidExpr q -> ValidExpr (mkEqExpr p q)
  validEqTrans :
    ∀ p q r : DbExpr,
      ValidExpr (mkEqExpr p q) ->
      ValidExpr (mkEqExpr q r) ->
      ValidExpr (mkEqExpr p r)
  validEqMp :
    ∀ p q : DbExpr,
      ValidExpr (mkEqExpr p q) ->
      ValidExpr p ->
      ValidExpr q
  validEqCongrApp :
    ∀ f g x y : DbExpr,
      ValidExpr (mkEqExpr f g) ->
      ValidExpr (mkEqExpr x y) ->
      ValidExpr (mkCombEqExpr f g x y)
  validEqCongrLam :
    ∀ n : Lean.Name, ∀ ty s t : DbExpr,
      ValidExpr (mkEqExpr s t) ->
      ValidExpr (mkAbsEqExpr n ty s t)
  validBeta :
    ∀ r : TypedBetaRedex,
      betaBinderAgreement r ->
      ValidExpr (mkEqExpr (betaRedexExpr r) (typedBetaContract r))

abbrev Valid (m : Model) (s : Sequent) : Prop :=
  (forall h, h ∈ s.hyps -> m.ValidExpr h) -> m.ValidExpr s.concl

abbrev ValidThm (m : Model) (th : Thm) : Prop :=
  Valid m th.seq

structure ModelSubstLaws (m : Model) where
  typeSubstPreservesValid :
    ∀ (k : KernelState) (theta : TypeSubst) (s : Sequent),
      valid_ty_subst theta ->
      admissible_ty_image k.T theta ->
      typing_preserved_under_ty_subst theta s ->
      def_inst_coherent theta s ->
      const_instance_ok theta s ->
      theorem_structure_preserved theta s ->
      Valid m s ->
      Valid m (applyTypeSubstSequent theta s)
  termSubstPreservesValid :
    ∀ (sigma : TermSubst) (s : Sequent),
      valid_term_subst sigma ->
      Valid m s ->
      Valid m (applyTermSubstSequent sigma s)

structure ModelAlphaLaws (m : Model) where
  alphaRespect :
    ∀ {e1 e2 : DbExpr},
      AlphaEqExpr e1 e2 ->
      m.ValidExpr e1 ->
      m.ValidExpr e2

structure ModelLawBundle (m : Model) where
  subst : ModelSubstLaws m
  alpha : ModelAlphaLaws m

theorem bundle_inst_type_capsule
    (m : Model)
    (bundle : ModelLawBundle m)
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hSubst : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : def_inst_coherent theta s)
    (hConst : const_instance_ok theta s)
    (hStruct : theorem_structure_preserved theta s)
    (hValid : Valid m s) :
    Valid m (applyTypeSubstSequent theta s) := by
  exact bundle.subst.typeSubstPreservesValid
    k theta s hSubst hImg hTyping hDef hConst hStruct hValid

theorem bundle_inst_term_capsule
    (m : Model)
    (bundle : ModelLawBundle m)
    (sigma : TermSubst)
    (s : Sequent)
    (hSubst : valid_term_subst sigma)
    (hValid : Valid m s) :
    Valid m (applyTermSubstSequent sigma s) := by
  exact bundle.subst.termSubstPreservesValid sigma s hSubst hValid

theorem bundle_alpha_capsule
    (m : Model)
    (bundle : ModelLawBundle m)
    {e1 e2 : DbExpr}
    (hAlpha : AlphaEqExpr e1 e2)
    (hValid : m.ValidExpr e1) :
    m.ValidExpr e2 := by
  exact bundle.alpha.alphaRespect hAlpha hValid

end QEDFV
