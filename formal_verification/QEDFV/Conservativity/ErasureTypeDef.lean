import QEDFV.Conservativity.ErasureSpec

namespace QEDFV

mutual

def erase_typedef (k : TyCon) : DerivationObj -> DerivationObj
  | .leaf s => .leaf s
  | .rule r ds s => .rule r (erase_typedef_list k ds) s
  | .gate .typeDefGate cert d s =>
      if cert = k then erase_typedef k d else .gate .typeDefGate cert (erase_typedef k d) s
  | .gate g cert d s => .gate g cert (erase_typedef k d) s

def erase_typedef_list (k : TyCon) : List DerivationObj -> List DerivationObj
  | [] => []
  | d :: ds => erase_typedef k d :: erase_typedef_list k ds

end

theorem erase_typedef_list_mem
    (k : TyCon) :
    ∀ ds d', d' ∈ erase_typedef_list k ds -> ∃ d0, d0 ∈ ds ∧ erase_typedef k d0 = d'
  | [], d', hMem => by
      cases hMem
  | d :: ds, d', hMem => by
      simp [erase_typedef_list] at hMem
      rcases hMem with hHead | hTail
      · exact ⟨d, by simp, hHead.symm⟩
      · rcases erase_typedef_list_mem k ds d' hTail with ⟨d0, hd0, hEq⟩
        exact ⟨d0, by simp [hd0], hEq⟩

theorem erase_typedef_correct_aux
    (ks : KernelState)
    (k : TyCon) :
    ∀ d s, Derives ks d s -> Derives ks (erase_typedef k d) s
  | .leaf _, s, hDerives => by
      simpa [erase_typedef] using hDerives
  | .rule r ds seq, s, hDerives => by
      simp [Derives, erase_typedef] at hDerives ⊢
      rcases hDerives with ⟨hTarget, hDer, hChildren⟩
      refine ⟨hTarget, hDer, ?_⟩
      intro d' hd'
      rcases erase_typedef_list_mem k ds d' hd' with ⟨d0, hd0in, hd0eq⟩
      rcases hChildren d0 hd0in with ⟨sp, hDer0⟩
      refine ⟨sp, ?_⟩
      simpa [hd0eq] using erase_typedef_correct_aux ks k d0 sp hDer0
  | .gate g cert d _, s, hDerives => by
      simp [Derives] at hDerives
      rcases hDerives with ⟨hTarget, hChild⟩
      subst hTarget
      cases g with
      | typeDefGate =>
          by_cases hEq : cert = k
          · simpa [erase_typedef, Derives, hEq] using erase_typedef_correct_aux ks k d s hChild
          · simpa [erase_typedef, Derives, hEq] using erase_typedef_correct_aux ks k d s hChild
      | defGate =>
          simpa [erase_typedef, Derives] using erase_typedef_correct_aux ks k d s hChild
      | specGate =>
          simpa [erase_typedef, Derives] using erase_typedef_correct_aux ks k d s hChild

theorem erase_typedef_correct
    (ks : KernelState)
    (t0 : TheoryState)
    (k : TyCon)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives ks d s)
    (_hOld : OldLang t0 s) :
    Derives ks (erase_typedef k d) s := by
  exact erase_typedef_correct_aux ks k d s hDerives

end QEDFV
