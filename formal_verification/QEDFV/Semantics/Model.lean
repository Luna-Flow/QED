import QEDFV.Kernel.PrimitiveRules

namespace QEDFV

structure Model where
  ValidExpr : DbExpr -> Prop
  validEqRefl : ∀ t : DbExpr, ValidExpr (mkEqExpr t t)
  validEqIntro : ∀ p q : DbExpr, ValidExpr p -> ValidExpr q -> ValidExpr (mkEqExpr p q)

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

end QEDFV
