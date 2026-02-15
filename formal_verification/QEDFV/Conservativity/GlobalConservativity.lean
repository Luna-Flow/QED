import QEDFV.Conservativity.ErasureTypeDef

namespace QEDFV

inductive ExtensionStep where
  | defStep : ConstName -> ExtensionStep
  | specStep : ConstName -> ExtensionStep
  | typeDefStep : TyCon -> ExtensionStep
deriving Repr, BEq

def eraseStep : ExtensionStep -> DerivationObj -> DerivationObj
  | .defStep h => erase_def h
  | .specStep h => erase_spec h
  | .typeDefStep k => erase_typedef k

def eraseSequence : List ExtensionStep -> DerivationObj -> DerivationObj
  | [], d => d
  | step :: rest, d => eraseSequence rest (eraseStep step d)

theorem eraseSequence_append
    (stepsL stepsR : List ExtensionStep)
    (d : DerivationObj) :
    eraseSequence (stepsL ++ stepsR) d =
      eraseSequence stepsR (eraseSequence stepsL d) := by
  induction stepsL generalizing d with
  | nil =>
      simp [eraseSequence]
  | cons step rest ih =>
      simp [eraseSequence, ih]

theorem eraseStep_preserves_derivability
    (ks : KernelState)
    (t0 : TheoryState)
    (step : ExtensionStep)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (hOld : OldLang t0 s) :
    Derives ks (eraseStep step d) s := by
  cases step with
  | defStep h =>
      simpa [eraseStep] using erase_def_correct ks t0 h d s hDerives hOld
  | specStep h =>
      simpa [eraseStep] using erase_spec_correct ks t0 h d s hDerives hOld
  | typeDefStep k =>
      simpa [eraseStep] using erase_typedef_correct ks t0 k d s hDerives hOld

theorem eraseSequence_preserves_derivability
    (ks : KernelState)
    (t0 : TheoryState)
    (steps : List ExtensionStep)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (hOld : OldLang t0 s) :
    Derives ks (eraseSequence steps d) s := by
  induction steps generalizing d with
  | nil =>
      simpa [eraseSequence] using hDerives
  | cons step rest ih =>
      simp [eraseSequence]
      apply ih
      exact eraseStep_preserves_derivability ks t0 step d s hDerives hOld

theorem global_conservativity_finite_step
    (ks : KernelState)
    (t0 : TheoryState)
    (steps : List ExtensionStep)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (hOld : OldLang t0 s) :
    Derives ks (eraseSequence steps d) s := by
  exact eraseSequence_preserves_derivability ks t0 steps d s hDerives hOld

theorem global_conservativity_finite_step_split
    (ks : KernelState)
    (t0 : TheoryState)
    (stepsL stepsR : List ExtensionStep)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (hOld : OldLang t0 s) :
    Derives ks (eraseSequence (stepsL ++ stepsR) d) s := by
  have hL : Derives ks (eraseSequence stepsL d) s :=
    eraseSequence_preserves_derivability ks t0 stepsL d s hDerives hOld
  have hR : Derives ks (eraseSequence stepsR (eraseSequence stepsL d)) s :=
    eraseSequence_preserves_derivability ks t0 stepsR (eraseSequence stepsL d) s hL hOld
  simpa [eraseSequence_append] using hR

end QEDFV
