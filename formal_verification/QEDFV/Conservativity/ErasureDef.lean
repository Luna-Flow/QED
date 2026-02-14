import QEDFV.Conservativity.DerivationObject

namespace QEDFV

def erase_def (h : ConstName) : DerivationObj -> DerivationObj
  | .gate .defGate cert d s =>
      if cert = h then erase_def h d else .gate .defGate cert (erase_def h d) s
  | .gate g cert d s => .gate g cert (erase_def h d) s
  | d => d

theorem erase_def_size_le_aux (h : ConstName) :
    forall d : DerivationObj, derivationSize (erase_def h d) <= derivationSize d
  | .leaf _ => by
      simp [erase_def, derivationSize]
  | .rule _ _ _ => by
      simp [erase_def, derivationSize]
  | .gate g cert d _ => by
      cases g with
      | defGate =>
          by_cases hEq : cert = h
          · simp [erase_def, derivationSize, hEq]
            have hs : derivationSize d <= 1 + derivationSize d := by
              exact Nat.le_add_left (derivationSize d) 1
            exact Nat.le_trans (erase_def_size_le_aux h d) hs
          · simp [erase_def, derivationSize, hEq, erase_def_size_le_aux h d]
      | specGate =>
          simp [erase_def, derivationSize, erase_def_size_le_aux h d]
      | typeDefGate =>
          simp [erase_def, derivationSize, erase_def_size_le_aux h d]

theorem erase_def_size_le (h : ConstName) (d : DerivationObj) :
    derivationSize (erase_def h d) <= derivationSize d := by
  exact erase_def_size_le_aux h d

theorem erase_def_correct_aux
    (k : KernelState)
    (t0 : TheoryState)
    (h : ConstName) :
    forall d s, Derives k d s -> OldLang t0 s -> Derives k (erase_def h d) s
  | .leaf _, s, hDerives, _ => by
      simpa [erase_def] using hDerives
  | .rule _ _ _, s, hDerives, _ => by
      simpa [erase_def] using hDerives
  | .gate g cert d _, s, hDerives, hOld => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      cases g with
      | defGate =>
          by_cases hEq : cert = h
          · simpa [erase_def, hEq] using erase_def_correct_aux k t0 h d s hChild hOld
          · simp [erase_def, hEq, Derives]
            exact erase_def_correct_aux k t0 h d s hChild hOld
      | specGate =>
          simp [erase_def, Derives]
          exact erase_def_correct_aux k t0 h d s hChild hOld
      | typeDefGate =>
          simp [erase_def, Derives]
          exact erase_def_correct_aux k t0 h d s hChild hOld

theorem erase_def_correct
    (k : KernelState)
    (t0 : TheoryState)
    (h : ConstName)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives k d s)
    (hOld : OldLang t0 s) :
    Derives k (erase_def h d) s := by
  exact erase_def_correct_aux k t0 h d s hDerives hOld

end QEDFV
