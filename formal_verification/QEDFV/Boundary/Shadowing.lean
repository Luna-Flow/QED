import QEDFV.Boundary.Conversion
import QEDFV.Signature.ScopedStack

namespace QEDFV

def lookupShadowingDeterminism (s : ScopeStack) (c : ConstName) : Prop :=
  forall t1 t2, lookup s c = some t1 -> lookup s c = some t2 -> t1 = t2

def outerRestorationByPop (s : ScopeStack) : Prop :=
  forall c ty s2,
    add? (push s) c ty = some s2 ->
    pop? s2 = some s ->
    lookup (match pop? s2 with | some s' => s' | none => s) c = lookup s c

def scopeLocalUniqueness (s : ScopeStack) : Prop :=
  forall c ty, inTop s c = true -> add? s c ty = none

theorem shadowing_determinism (s : ScopeStack) (c : ConstName) :
    lookupShadowingDeterminism s c := by
  intro t1 t2 h1 h2
  exact lookup_deterministic s c t1 t2 h1 h2

theorem scope_restoration_after_pop (s : ScopeStack) : outerRestorationByPop s := by
  intro c ty s2 hadd hpop
  simp [hpop]

theorem scope_local_uniqueness (s : ScopeStack) : scopeLocalUniqueness s := by
  intro c ty hInTop
  unfold add?
  by_cases hmem : c ∈ Reserved
  · simp [hmem]
  · cases hs : s.frames with
    | nil =>
        simp [inTop, hs] at hInTop
    | cons f rest =>
        unfold inTop at hInTop
        simp [hs] at hInTop
        simp [hmem, hInTop]

end QEDFV
