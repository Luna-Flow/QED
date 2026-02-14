import QEDFV.Semantics.Model

namespace QEDFV

structure AdmissibleModelClass (t : TheoryState) where
  model : Model
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
