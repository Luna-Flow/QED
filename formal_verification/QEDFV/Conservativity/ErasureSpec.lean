import QEDFV.Conservativity.ErasureDef

namespace QEDFV

def erase_spec (h : ConstName) : DerivationObj -> DerivationObj
  | .gate .specGate cert d s =>
      if cert = h then erase_spec h d else .gate .specGate cert (erase_spec h d) s
  | .gate g cert d s => .gate g cert (erase_spec h d) s
  | d => d

theorem erase_spec_correct_aux
    (k : KernelState)
    (t0 : TheoryState)
    (h : ConstName) :
    forall d s, Derives k d s -> OldLang t0 s -> Derives k (erase_spec h d) s
  | .leaf _, s, hDerives, _ => by
      simpa [erase_spec] using hDerives
  | .rule _ _ _, s, hDerives, _ => by
      simpa [erase_spec] using hDerives
  | .gate g cert d _, s, hDerives, hOld => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      cases g with
      | specGate =>
          by_cases hEq : cert = h
          · simpa [erase_spec, hEq] using erase_spec_correct_aux k t0 h d s hChild hOld
          · simp [erase_spec, hEq, Derives]
            exact erase_spec_correct_aux k t0 h d s hChild hOld
      | defGate =>
          simp [erase_spec, Derives]
          exact erase_spec_correct_aux k t0 h d s hChild hOld
      | typeDefGate =>
          simp [erase_spec, Derives]
          exact erase_spec_correct_aux k t0 h d s hChild hOld

theorem erase_spec_correct
    (k : KernelState)
    (t0 : TheoryState)
    (h : ConstName)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives k d s)
    (hOld : OldLang t0 s) :
    Derives k (erase_spec h d) s := by
  exact erase_spec_correct_aux k t0 h d s hDerives hOld

end QEDFV
