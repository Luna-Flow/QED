import QEDFV.Kernel.PrimitiveRules

namespace QEDFV

structure Model where
  ValidExpr : DbExpr -> Prop
  soundDerivable : ∀ {k : KernelState} {s : Sequent}, Derivable k s -> ValidExpr s.concl

abbrev Valid (m : Model) (s : Sequent) : Prop :=
  (forall h, h ∈ s.hyps -> m.ValidExpr h) -> m.ValidExpr s.concl

abbrev ValidThm (m : Model) (th : Thm) : Prop :=
  Valid m th.seq

end QEDFV
