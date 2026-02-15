import QEDFV.Extension.SpecOK

namespace QEDFV

inductive GateKind where
  | defGate
  | typeDefGate
  | specGate
deriving Repr, BEq

inductive DerivationObj where
  | leaf : Sequent -> DerivationObj
  | rule : String -> List DerivationObj -> Sequent -> DerivationObj
  | gate : GateKind -> String -> DerivationObj -> Sequent -> DerivationObj
deriving Repr

def Derives (k : KernelState) : DerivationObj -> Sequent -> Prop
  | .leaf s, target => target = s ∧ Derivable k s
  | .rule _ ds s, target =>
      target = s ∧ Derivable k s ∧ ∀ d, d ∈ ds -> ∃ sp, Derives k d sp
  | .gate _ _ d s, target =>
      target = s ∧ Derives k d s

def OldLang (_t0 : TheoryState) (s : Sequent) : Prop :=
  QEDExprWF s.concl ∧ ∀ h, h ∈ s.hyps -> QEDExprWF h

def derivationSize : DerivationObj -> Nat
  | .leaf _ => 1
  | .rule _ ds _ => 1 + ds.foldr (fun d acc => derivationSize d + acc) 0
  | .gate _ _ d _ => 1 + derivationSize d

theorem derives_leaf_iff (k : KernelState) (s target : Sequent) :
    Derives k (.leaf s) target ↔ target = s ∧ Derivable k s := by
  simp [Derives]

theorem derives_gate_iff
    (k : KernelState)
    (g : GateKind)
    (cert : String)
    (d : DerivationObj)
    (s target : Sequent) :
    Derives k (.gate g cert d s) target ↔ target = s ∧ Derives k d s := by
  simp [Derives]

theorem derives_implies_derivable
    (k : KernelState) :
    ∀ d s, Derives k d s -> Derivable k s
  | .leaf _, s, hDerives => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hDerivable⟩
      subst hTarget
      exact hDerivable
  | .rule _ _ seq, s, hDerives => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hDerivable, _hChildren⟩
      subst hTarget
      exact hDerivable
  | .gate _ _ d seq, s, hDerives => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      exact derives_implies_derivable k d _ hChild

end QEDFV
