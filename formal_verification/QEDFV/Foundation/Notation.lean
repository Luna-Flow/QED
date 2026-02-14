namespace QEDFV

abbrev HolName := String
abbrev TVar := String
abbrev TyCon := String
abbrev ConstName := String
abbrev TypeArity := Nat
abbrev Finset (alpha : Type u) := List alpha

namespace FSet

def mem [DecidableEq alpha] (a : alpha) (s : Finset alpha) : Bool :=
  s.contains a

def insert [DecidableEq alpha] (a : alpha) (s : Finset alpha) : Finset alpha :=
  if s.contains a then s else a :: s

def subset [DecidableEq alpha] (s1 s2 : Finset alpha) : Prop :=
  forall x, x ∈ s1 -> x ∈ s2

def erase [DecidableEq alpha] (a : alpha) (s : Finset alpha) : Finset alpha :=
  s.erase a

end FSet

end QEDFV
