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

abbrev AlphaEqExpr (e1 e2 : DbExpr) : Prop := e1 = e2

def alphaSetEq (s1 s2 : Finset DbExpr) : Prop :=
  ∀ e, e ∈ s1 ↔ e ∈ s2

def hypsUnion (s1 s2 : Finset DbExpr) : Finset DbExpr :=
  s1 ++ s2

def hypsRemove (s : Finset DbExpr) (e : DbExpr) : Finset DbExpr :=
  s.filter (fun x => x != e)

theorem hypsUnion_idempotent (s : Finset DbExpr) :
    alphaSetEq (hypsUnion s s) s := by
  intro e
  constructor
  · intro h
    exact List.mem_append.mp h |>.elim id id
  · intro h
    exact List.mem_append.mpr (Or.inl h)

theorem hypsUnion_commutative (s1 s2 : Finset DbExpr) :
    alphaSetEq (hypsUnion s1 s2) (hypsUnion s2 s1) := by
  intro e
  constructor
  · intro h
    rcases List.mem_append.mp h with h1 | h2
    · exact List.mem_append.mpr (Or.inr h1)
    · exact List.mem_append.mpr (Or.inl h2)
  · intro h
    rcases List.mem_append.mp h with h2 | h1
    · exact List.mem_append.mpr (Or.inr h2)
    · exact List.mem_append.mpr (Or.inl h1)

theorem hypsRemove_alpha_compatible
    (s : Finset DbExpr)
    (a b : DbExpr)
    (hAlpha : AlphaEqExpr a b) :
    alphaSetEq (hypsRemove s a) (hypsRemove s b) := by
  subst hAlpha
  intro e
  rfl

def assumptionsAsAlphaQuotients (th : Thm) : Prop :=
  alphaSetEq (hypsUnion th.seq.hyps th.seq.hyps) th.seq.hyps

end QEDFV
