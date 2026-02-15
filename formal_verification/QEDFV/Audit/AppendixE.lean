import QEDFV.Db.TypedBeta
import QEDFV.Kernel.PrimitiveRules
import QEDFV.Boundary.Conversion

namespace QEDFV

def audit_e1_typed_core_injectivity : Prop :=
  forall n1 n2 t1 t2 b1 b2 bi1 bi2,
    Lean.Expr.lam n1 t1 b1 bi1 = Lean.Expr.lam n2 t2 b2 bi2 ->
    t1 = t2 ∧ b1 = b2

theorem audit_e1_typed_core_injectivity_proved : audit_e1_typed_core_injectivity := by
  intro n1 n2 t1 t2 b1 b2 bi1 bi2 h
  exact typed_core_injectivity n1 n2 t1 t2 b1 b2 bi1 bi2 h

def audit_e2_trans_middle_term_guard : Prop :=
  forall k A B x y y' z,
    A.concl = mkEqExpr x y ->
    B.concl = mkEqExpr y' z ->
    AlphaEqExpr y y' ->
    Derivable k A ->
    Derivable k B ->
    Derivable k { hyps := hypsUnion A.hyps B.hyps, concl := mkEqExpr x z }

theorem audit_e2_trans_middle_term_guard_proved : audit_e2_trans_middle_term_guard := by
  intro k A B x y y' z hEqA hEqB hMid hA hB
  exact Derivable.trans (k := k) A B x y y' z hEqA hEqB hMid hA hB

def audit_e3_beta_binder_agreement : Prop := appendixE_beta_binder_agreement_obligation

def audit_e4_boundary_lift_type_coherence : Prop :=
  forall (bc : BoundaryConversion), forall (_h : BoundaryLaws bc),
    forall (t : Term), forall (d : DbExpr),
      bc.lowerTerm t = some d ->
      exists t', bc.liftTerm d = some t' ∧ AlphaEq t' t

theorem audit_e4_boundary_lift_type_coherence_proved : audit_e4_boundary_lift_type_coherence := by
  intro bc h t d hLower
  exact h.denotationPreservationTerm t d hLower

end QEDFV
