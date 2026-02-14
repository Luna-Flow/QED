import QEDFV.Boundary.Shadowing

namespace QEDFV

structure Sequent where
  hyps : Finset DbExpr
  concl : DbExpr
deriving Repr

structure Thm where
  seq : Sequent
deriving Repr

def thmHyps (th : Thm) : Finset DbExpr := th.seq.hyps
def thmConcl (th : Thm) : DbExpr := th.seq.concl

def assumptionsAsAlphaQuotients (th : Thm) : Prop :=
  th.seq.hyps = th.seq.hyps

end QEDFV
