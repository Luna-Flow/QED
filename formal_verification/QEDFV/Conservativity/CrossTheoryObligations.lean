import QEDFV.Conservativity.GlobalConservativity

namespace QEDFV

/-
The existing erase_* theorems preserve `Derives ks` for one fixed state `ks`.
That is a tree-rewriting result, not a conservativity theorem between two theories.
The missing cross-state simulation is recorded explicitly here. In particular,
neither `OldLang` nor `Derives` in DerivationObject currently supplies this law.
-/

structure CrossTheoryErasure
    (base extended : KernelState) (step : ExtensionStep) where
  oldLanguage : Sequent → Prop
  erases : ∀ d s,
    Derives extended d s →
    oldLanguage s →
    Derives base (eraseStep step d) s

theorem conservativity_of_cross_theory_erasure
    (base extended : KernelState)
    (step : ExtensionStep)
    (simulation : CrossTheoryErasure base extended step)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives extended d s)
    (hOld : simulation.oldLanguage s) :
    Derivable base s := by
  exact derives_implies_derivable base _ _ (simulation.erases d s hDerives hOld)

end QEDFV
