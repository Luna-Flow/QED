import QEDFV.Signature.ScopedStack

namespace QEDFV

structure TheoryState where
  defHeads : Finset ConstName
  tySymbols : Finset (TyCon × TypeArity)
  committedConsts : Finset ConstName
deriving Repr, BEq

structure KernelState where
  T : TheoryState
  S : ScopeStack
deriving Repr, BEq

def emptyTheoryState : TheoryState :=
  { defHeads := [], tySymbols := [("bool", 0), ("fun", 2), ("ind", 0)], committedConsts := [] }

def emptyKernelState : KernelState :=
  { T := emptyTheoryState, S := emptyScopeStack }

def DefHeads (t : TheoryState) : Finset ConstName := t.defHeads

def commitDefHead (t : TheoryState) (c : ConstName) : TheoryState :=
  if c ∈ t.defHeads then t
  else { t with defHeads := c :: t.defHeads, committedConsts := c :: t.committedConsts }

def ksPushScope (k : KernelState) : KernelState :=
  { k with S := push k.S }

def ksPopScope? (k : KernelState) : Option KernelState :=
  match pop? k.S with
  | some s' => some { k with S := s' }
  | none => none

theorem scope_pop_invariant_defheads (k k' : KernelState) :
    ksPopScope? k = some k' -> DefHeads k'.T = DefHeads k.T := by
  intro h
  unfold ksPopScope? at h
  cases hpop : pop? k.S <;> simp [hpop] at h
  cases h
  rfl

theorem defheads_monotone_commit (t : TheoryState) (c : ConstName) :
    forall x, x ∈ DefHeads t -> x ∈ DefHeads (commitDefHead t c) := by
  intro x hx
  by_cases h : c ∈ t.defHeads
  · simpa [DefHeads, commitDefHead, h] using hx
  · have hheads : DefHeads (commitDefHead t c) = c :: DefHeads t := by
      simp [DefHeads, commitDefHead, h]
    rw [hheads]
    exact List.mem_cons_of_mem _ hx

end QEDFV
