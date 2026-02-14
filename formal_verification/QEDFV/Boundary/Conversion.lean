import QEDFV.Db.TypedBeta
import QEDFV.Term.Grammar

namespace QEDFV

abbrev AlphaEq (t1 t2 : Term) : Prop := t1 = t2
abbrev DbEq (d1 d2 : DbExpr) : Prop := d1 = d2

structure BoundaryConversion where
  lowerTerm : Term -> Option DbExpr
  liftTerm : DbExpr -> Option Term
  lowerSequent : List Term -> Term -> Option (List DbExpr × DbExpr)
  liftSequent : List DbExpr -> DbExpr -> Option (List Term × Term)

structure BoundaryLaws (bc : BoundaryConversion) where
  alphaInvariantLowering :
    ∀ t1 t2 d1 d2,
      AlphaEq t1 t2 ->
      bc.lowerTerm t1 = some d1 ->
      bc.lowerTerm t2 = some d2 ->
      DbEq d1 d2
  roundTripUpToAlpha :
    ∀ t d,
      bc.lowerTerm t = some d ->
      ∃ t', bc.liftTerm d = some t' ∧ AlphaEq t' t
  liftChoiceCongruence :
    ∀ d1 d2 t1 t2,
      DbEq d1 d2 ->
      bc.liftTerm d1 = some t1 ->
      bc.liftTerm d2 = some t2 ->
      AlphaEq t1 t2
  denotationPreservationTerm :
    ∀ t d,
      bc.lowerTerm t = some d ->
      ∃ t', bc.liftTerm d = some t' ∧ AlphaEq t' t
  denotationPreservationSequent :
    ∀ hs c dhs dc,
      bc.lowerSequent hs c = some (dhs, dc) ->
      ∃ hs' c', bc.liftSequent dhs dc = some (hs', c')
  semanticRuleLiftingSafety :
    ∀ hs c dhs dc,
      bc.lowerSequent hs c = some (dhs, dc) ->
      bc.liftSequent dhs dc ≠ none

abbrev boundaryConversionTotalityObligation (bc : BoundaryConversion) : Prop :=
  forall t, (bc.lowerTerm t).isSome

end QEDFV
