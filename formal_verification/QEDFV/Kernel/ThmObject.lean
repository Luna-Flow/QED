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

def alphaNorm : DbExpr -> DbExpr
  | .bvar i => .bvar i
  | .const n ls => .const n ls
  | .app f a => .app (alphaNorm f) (alphaNorm a)
  | .lam _ ty body bi => .lam .anonymous (alphaNorm ty) (alphaNorm body) bi
  | e => e

def AlphaEqExpr (e1 e2 : DbExpr) : Prop :=
  alphaNorm e1 = alphaNorm e2

theorem alphaEq_refl (e : DbExpr) : AlphaEqExpr e e := by
  rfl

theorem alphaEq_symm {e1 e2 : DbExpr} :
    AlphaEqExpr e1 e2 -> AlphaEqExpr e2 e1 := by
  intro h
  exact Eq.symm h

theorem alphaEq_trans {e1 e2 e3 : DbExpr} :
    AlphaEqExpr e1 e2 -> AlphaEqExpr e2 e3 -> AlphaEqExpr e1 e3 := by
  intro h12 h23
  exact Eq.trans h12 h23

def memAlpha (e : DbExpr) (s : Finset DbExpr) : Prop :=
  ∃ e', e' ∈ s ∧ AlphaEqExpr e e'

def alphaSetEq (s1 s2 : Finset DbExpr) : Prop :=
  ∀ e, memAlpha e s1 ↔ memAlpha e s2

def hypsUnion (s1 s2 : Finset DbExpr) : Finset DbExpr :=
  s1 ++ s2

def hypsRemove (s : Finset DbExpr) (e : DbExpr) : Finset DbExpr :=
  s.filter (fun x => alphaNorm x != alphaNorm e)

abbrev AlphaAssumptions := Finset DbExpr

def alphaMember (e : DbExpr) (Γ : AlphaAssumptions) : Prop :=
  memAlpha e Γ

def alphaUnion (Γ Δ : AlphaAssumptions) : AlphaAssumptions :=
  hypsUnion Γ Δ

def alphaRemove (Γ : AlphaAssumptions) (e : DbExpr) : AlphaAssumptions :=
  hypsRemove Γ e

def alphaAssumptionEq (Γ Δ : AlphaAssumptions) : Prop :=
  alphaSetEq Γ Δ

theorem alphaMember_singleton_self (e : DbExpr) : alphaMember e [e] := by
  exact ⟨e, by simp, alphaEq_refl e⟩

theorem hypsUnion_idempotent (s : Finset DbExpr) :
    alphaSetEq (hypsUnion s s) s := by
  intro e
  constructor
  · intro hMem
    rcases hMem with ⟨e', hIn, hAlpha⟩
    rcases List.mem_append.mp hIn with hL | hR
    · exact ⟨e', hL, hAlpha⟩
    · exact ⟨e', hR, hAlpha⟩
  · intro hMem
    rcases hMem with ⟨e', hIn, hAlpha⟩
    exact ⟨e', List.mem_append.mpr (Or.inl hIn), hAlpha⟩

theorem hypsUnion_commutative (s1 s2 : Finset DbExpr) :
    alphaSetEq (hypsUnion s1 s2) (hypsUnion s2 s1) := by
  intro e
  constructor
  · intro hMem
    rcases hMem with ⟨e', hIn, hAlpha⟩
    rcases List.mem_append.mp hIn with h1 | h2
    · exact ⟨e', List.mem_append.mpr (Or.inr h1), hAlpha⟩
    · exact ⟨e', List.mem_append.mpr (Or.inl h2), hAlpha⟩
  · intro hMem
    rcases hMem with ⟨e', hIn, hAlpha⟩
    rcases List.mem_append.mp hIn with h2 | h1
    · exact ⟨e', List.mem_append.mpr (Or.inr h2), hAlpha⟩
    · exact ⟨e', List.mem_append.mpr (Or.inl h1), hAlpha⟩

theorem hypsRemove_alpha_compatible
    (s : Finset DbExpr)
    (a b : DbExpr)
    (hAlpha : AlphaEqExpr a b) :
    alphaSetEq (hypsRemove s a) (hypsRemove s b) := by
  intro e
  unfold memAlpha
  constructor <;> intro hMem <;> rcases hMem with ⟨e', hIn, hEq⟩
  · refine ⟨e', ?_, hEq⟩
    have hKeep : (alphaNorm e' != alphaNorm a) = true := by
      exact List.mem_filter.mp hIn |>.right
    have hNorm : alphaNorm a = alphaNorm b := hAlpha
    have hKeep' : (alphaNorm e' != alphaNorm b) = true := by
      simpa [hNorm] using hKeep
    exact List.mem_filter.mpr ⟨List.mem_filter.mp hIn |>.left, hKeep'⟩
  · refine ⟨e', ?_, hEq⟩
    have hKeep : (alphaNorm e' != alphaNorm b) = true := by
      exact List.mem_filter.mp hIn |>.right
    have hNorm : alphaNorm a = alphaNorm b := hAlpha
    have hKeep' : (alphaNorm e' != alphaNorm a) = true := by
      simpa [hNorm] using hKeep
    exact List.mem_filter.mpr ⟨List.mem_filter.mp hIn |>.left, hKeep'⟩

theorem alphaUnion_idempotent (Γ : AlphaAssumptions) :
    alphaAssumptionEq (alphaUnion Γ Γ) Γ := by
  exact hypsUnion_idempotent Γ

theorem alphaUnion_commutative (Γ Δ : AlphaAssumptions) :
    alphaAssumptionEq (alphaUnion Γ Δ) (alphaUnion Δ Γ) := by
  exact hypsUnion_commutative Γ Δ

theorem alphaRemove_compatible
    (Γ : AlphaAssumptions)
    (a b : DbExpr)
    (hAlpha : AlphaEqExpr a b) :
    alphaAssumptionEq (alphaRemove Γ a) (alphaRemove Γ b) := by
  exact hypsRemove_alpha_compatible Γ a b hAlpha

def assumptionsAsAlphaQuotients (th : Thm) : Prop :=
  alphaAssumptionEq (alphaUnion th.seq.hyps th.seq.hyps) th.seq.hyps

end QEDFV
