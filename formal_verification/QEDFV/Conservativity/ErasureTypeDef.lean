import QEDFV.Conservativity.ErasureSpec

namespace QEDFV

def erase_typedef (k : TyCon) : DerivationObj -> DerivationObj
  | .gate .typeDefGate cert d s =>
      if cert = k then erase_typedef k d else .gate .typeDefGate cert (erase_typedef k d) s
  | .gate g cert d s => .gate g cert (erase_typedef k d) s
  | d => d

theorem erase_typedef_correct_aux
    (ks : KernelState)
    (t0 : TheoryState)
    (k : TyCon) :
    forall d s, Derives ks d s -> OldLang t0 s -> Derives ks (erase_typedef k d) s
  | .leaf _, s, hDerives, _ => by
      simpa [erase_typedef] using hDerives
  | .rule _ _ _, s, hDerives, _ => by
      simpa [erase_typedef] using hDerives
  | .gate g cert d _, s, hDerives, hOld => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      cases g with
      | typeDefGate =>
          by_cases hEq : cert = k
          · simpa [erase_typedef, hEq] using erase_typedef_correct_aux ks t0 k d s hChild hOld
          · simp [erase_typedef, hEq, Derives]
            exact erase_typedef_correct_aux ks t0 k d s hChild hOld
      | defGate =>
          simp [erase_typedef, Derives]
          exact erase_typedef_correct_aux ks t0 k d s hChild hOld
      | specGate =>
          simp [erase_typedef, Derives]
          exact erase_typedef_correct_aux ks t0 k d s hChild hOld

theorem erase_typedef_correct
    (ks : KernelState)
    (t0 : TheoryState)
    (k : TyCon)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (hOld : OldLang t0 s) :
    Derives ks (erase_typedef k d) s := by
  exact erase_typedef_correct_aux ks t0 k d s hDerives hOld

end QEDFV
