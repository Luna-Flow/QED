import QEDFV.Term.Grammar

namespace QEDFV

abbrev Frame := List (ConstName × HolType)

structure ScopeStack where
  frames : List Frame
deriving Repr, BEq

def Reserved : List ConstName := ["=", "@"]

def emptyScopeStack : ScopeStack :=
  { frames := [[]] }

def frameLookup (f : Frame) (c : ConstName) : Option HolType :=
  match f.find? (fun p => p.fst = c) with
  | some (_, ty) => some ty
  | none => none

def lookupFrames : List Frame -> ConstName -> Option HolType
  | [], _ => none
  | f :: rest, c =>
      match frameLookup f c with
      | some ty => some ty
      | none => lookupFrames rest c

def lookup (s : ScopeStack) (c : ConstName) : Option HolType :=
  lookupFrames s.frames c

def push (s : ScopeStack) : ScopeStack :=
  { frames := [] :: s.frames }

def pop? (s : ScopeStack) : Option ScopeStack :=
  match s.frames with
  | [] => none
  | [_] => none
  | _ :: rest => some { frames := rest }

def inTop (s : ScopeStack) (c : ConstName) : Bool :=
  match s.frames with
  | [] => false
  | f :: _ => (frameLookup f c).isSome

def add? (s : ScopeStack) (c : ConstName) (ty : HolType) : Option ScopeStack :=
  if Reserved.contains c then
    none
  else
    match s.frames with
    | [] => none
    | f :: rest =>
        if (frameLookup f c).isSome then
          none
        else
          some { frames := ((c, ty) :: f) :: rest }

def frameNoReserved (f : Frame) : Prop :=
  forall c ty, (c, ty) ∈ f -> c ∉ Reserved

def ScopedWF (s : ScopeStack) : Prop :=
  s.frames != [] ∧ forall f, f ∈ s.frames -> frameNoReserved f

theorem lookup_deterministic (s : ScopeStack) (c : ConstName)
    (t1 t2 : HolType) :
    lookup s c = some t1 -> lookup s c = some t2 -> t1 = t2 := by
  intro h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

theorem pop_of_push (s : ScopeStack) (h : s.frames ≠ []) :
    pop? (push s) = some s := by
  cases s with
  | mk frames =>
      cases frames with
      | nil =>
          contradiction
      | cons f rest =>
          simp [push, pop?]

theorem push_preserves_lookup (s : ScopeStack) (c : ConstName) :
    lookup (push s) c = lookup s c := by
  simp [lookup, lookupFrames, push, frameLookup]

end QEDFV
