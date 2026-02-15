import QEDFV.Conservativity.DerivationObject

namespace QEDFV

mutual

def erase_def (h : ConstName) : DerivationObj -> DerivationObj
  | .leaf s => .leaf s
  | .rule r ds s => .rule r (erase_def_list h ds) s
  | .gate .defGate cert d s =>
      if cert = h then erase_def h d else .gate .defGate cert (erase_def h d) s
  | .gate g cert d s => .gate g cert (erase_def h d) s

def erase_def_list (h : ConstName) : List DerivationObj -> List DerivationObj
  | [] => []
  | d :: ds => erase_def h d :: erase_def_list h ds

end

theorem erase_def_list_mem
    (h : ConstName) :
    ∀ ds d', d' ∈ erase_def_list h ds -> ∃ d0, d0 ∈ ds ∧ erase_def h d0 = d'
  | [], d', hMem => by
      cases hMem
  | d :: ds, d', hMem => by
      simp [erase_def_list] at hMem
      rcases hMem with hHead | hTail
      · exact ⟨d, by simp, hHead.symm⟩
      · rcases erase_def_list_mem h ds d' hTail with ⟨d0, hd0, hEq⟩
        exact ⟨d0, by simp [hd0], hEq⟩

theorem erase_def_correct_aux
    (k : KernelState)
    (h : ConstName) :
    ∀ d s, Derives k d s -> Derives k (erase_def h d) s
  | .leaf _, s, hDerives => by
      simpa [erase_def] using hDerives
  | .rule r ds seq, s, hDerives => by
      simp [Derives, erase_def] at hDerives ⊢
      rcases hDerives with ⟨hTarget, hDer, hChildren⟩
      refine ⟨hTarget, hDer, ?_⟩
      intro d' hd'
      rcases erase_def_list_mem h ds d' hd' with ⟨d0, hd0in, hd0eq⟩
      rcases hChildren d0 hd0in with ⟨sp, hDer0⟩
      refine ⟨sp, ?_⟩
      simpa [hd0eq] using erase_def_correct_aux k h d0 sp hDer0
  | .gate g cert d _, s, hDerives => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      cases g with
      | defGate =>
          by_cases hEq : cert = h
          · simpa [erase_def, Derives, hEq] using erase_def_correct_aux k h d s hChild
          · simpa [erase_def, Derives, hEq] using erase_def_correct_aux k h d s hChild
      | specGate =>
          simpa [erase_def, Derives] using erase_def_correct_aux k h d s hChild
      | typeDefGate =>
          simpa [erase_def, Derives] using erase_def_correct_aux k h d s hChild

theorem erase_def_correct
    (k : KernelState)
    (t0 : TheoryState)
    (h : ConstName)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives k d s)
    (_hOld : OldLang t0 s) :
    Derives k (erase_def h d) s := by
  exact erase_def_correct_aux k h d s hDerives

end QEDFV
