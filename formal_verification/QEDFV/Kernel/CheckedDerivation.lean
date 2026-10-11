import QEDFV.Kernel.PrimitiveRules

namespace QEDFV

/-
Unlike the legacy `DerivationObj` relation, this inductive object contains only
primitive rule premises and recursively checked child derivations.  It never
stores `Derivable k s` as an input premise.  The theorem below is the
reconstruction bridge into the kernel's derivability relation.
-/
inductive CheckedDerivation (k : KernelState) : Sequent -> Prop where
  | refl (t : DbExpr) :
      CheckedDerivation k { hyps := [], concl := mkEqExpr t t }
  | assume (p : DbExpr) :
      IsBoolExpr p ->
      alphaMember p [p] ->
      CheckedDerivation k { hyps := [p], concl := p }
  | trans (A B : Sequent) (x y y' z : DbExpr) :
      A.concl = mkEqExpr x y ->
      B.concl = mkEqExpr y' z ->
      transMiddleTypedCoreGuard y y' ->
      CheckedDerivation k A ->
      CheckedDerivation k B ->
      CheckedDerivation k { hyps := alphaUnion A.hyps B.hyps, concl := mkEqExpr x z }
  | mkComb (A B : Sequent) (f g x y : DbExpr) :
      A.concl = mkEqExpr f g ->
      B.concl = mkEqExpr x y ->
      CheckedDerivation k A ->
      CheckedDerivation k B ->
      CheckedDerivation k { hyps := alphaUnion A.hyps B.hyps, concl := mkCombEqExpr f g x y }
  | abs (A : Sequent) (n : Lean.Name) (ty s t : DbExpr) :
      A.concl = mkEqExpr s t ->
      (∀ h, h ∈ A.hyps -> ¬ dbHasLooseBVar h 0) ->
      CheckedDerivation k A ->
      CheckedDerivation k { hyps := A.hyps, concl := mkAbsEqExpr n ty s t }
  | beta (r : TypedBetaRedex) :
      betaTypedCoreGuard r ->
      CheckedDerivation k { hyps := [], concl := mkEqExpr (betaRedexExpr r) (typedBetaContract r) }
  | eqMp (A B : Sequent) (p q p' : DbExpr) :
      A.concl = mkEqExpr p q ->
      AlphaEqExpr p p' ->
      B.concl = p' ->
      IsBoolExpr p ->
      CheckedDerivation k A ->
      CheckedDerivation k B ->
      CheckedDerivation k { hyps := alphaUnion A.hyps B.hyps, concl := q }
  | deductAntisym (A B : Sequent) :
      alphaAssumptionEq
        (alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl))
        (alphaUnion A.hyps B.hyps) ->
      CheckedDerivation k A ->
      CheckedDerivation k B ->
      CheckedDerivation k
        { hyps := alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl)
        , concl := mkEqExpr A.concl B.concl
        }
  | instType (theta : TypeSubst) (A : Sequent) :
      valid_ty_subst theta ->
      admissible_ty_image k.T theta ->
      typeSubstObjectLevelSequent theta A ->
      typing_preserved_under_ty_subst theta A ->
      def_inst_coherent theta A ->
      const_instance_ok theta A ->
      theorem_structure_preserved theta A ->
      CheckedDerivation k A ->
      CheckedDerivation k (applyTypeSubstSequent theta A)
  | inst (sigma : TermSubst) (A : Sequent) :
      valid_term_subst sigma ->
      termSubstObjectLevelSequent sigma A ->
      CheckedDerivation k A ->
      CheckedDerivation k (applyTermSubstSequent sigma A)

theorem checked_derivation_sound (k : KernelState) :
    ∀ {s : Sequent}, CheckedDerivation k s -> Derivable k s
  | _, .refl t => Derivable.refl t
  | _, .assume p hBool hMember => Derivable.assume p hBool hMember
  | _, .trans A B x y y' z hEqA hEqB hMid hA hB =>
      Derivable.trans A B x y y' z hEqA hEqB hMid
        (checked_derivation_sound k hA) (checked_derivation_sound k hB)
  | _, .mkComb A B f g x y hEqA hEqB hA hB =>
      Derivable.mkComb A B f g x y hEqA hEqB
        (checked_derivation_sound k hA) (checked_derivation_sound k hB)
  | _, .abs A n ty s t hEq hNoLoose hA =>
      Derivable.abs A n ty s t hEq hNoLoose (checked_derivation_sound k hA)
  | _, .beta r hGuard => Derivable.beta r hGuard
  | _, .eqMp A B p q p' hEq hAlpha hPrem hBool hA hB =>
      Derivable.eqMp A B p q p' hEq hAlpha hPrem hBool
        (checked_derivation_sound k hA) (checked_derivation_sound k hB)
  | _, .deductAntisym A B hAlpha hA hB =>
      Derivable.deductAntisym A B hAlpha
        (checked_derivation_sound k hA) (checked_derivation_sound k hB)
  | _, .instType theta A hSubst hImg hObj hTyping hDef hConst hStruct hA =>
      Derivable.instType theta A hSubst hImg hObj hTyping hDef hConst hStruct
        (checked_derivation_sound k hA)
  | _, .inst sigma A hSubst hObj hA =>
      Derivable.inst sigma A hSubst hObj (checked_derivation_sound k hA)

end QEDFV
