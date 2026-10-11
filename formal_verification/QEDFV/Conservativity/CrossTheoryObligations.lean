import QEDFV.Conservativity.GlobalConservativity

namespace QEDFV

/-
The existing erase_* theorems preserve `Derives ks` for one fixed state `ks`.
That is a tree-rewriting result, not a conservativity theorem between two theories.
The missing cross-state simulation is recorded explicitly here. In particular,
neither `OldLang` nor `Derives` in DerivationObject currently supplies this law.
-/

/- This is an obligation supplied by a future gate-specific simulation.
   `erases` is the desired conclusion, not evidence from which the conclusion
   is independently derived.  No theorem in this file constructs it. -/
structure CrossTheoryErasureObligation
    (base extended : KernelState) (step : ExtensionStep) where
  oldLanguage : Sequent → Prop
  erases : ∀ d s,
    Derives extended d s →
    oldLanguage s →
    Derives base (eraseStep step d) s

/- A finite cross-theory simulation is the actual premise needed for the
   global theorem.  It deliberately quantifies over distinct base and
   extended states; no same-state erasure lemma can inhabit this structure. -/
structure CrossTheoryFiniteErasureObligation
    (base extended : KernelState) (steps : List ExtensionStep) where
  oldLanguage : Sequent → Prop
  erases : ∀ d s,
    Derives extended d s →
    oldLanguage s →
    Derives base (eraseSequence steps d) s

theorem derive_base_of_cross_theory_erasure_obligation
    (base extended : KernelState)
    (step : ExtensionStep)
    (obligation : CrossTheoryErasureObligation base extended step)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives extended d s)
    (hOld : obligation.oldLanguage s) :
    Derivable base s := by
  exact derives_implies_derivable base _ _ (obligation.erases d s hDerives hOld)

theorem derive_base_of_cross_theory_finite_erasure_obligation
    (base extended : KernelState)
    (steps : List ExtensionStep)
    (obligation : CrossTheoryFiniteErasureObligation base extended steps)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives extended d s)
    (hOld : obligation.oldLanguage s) :
    Derivable base s := by
  exact derives_implies_derivable base _ _ (obligation.erases d s hDerives hOld)

end QEDFV
