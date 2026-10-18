import QEDFV.HOL.Instantiation

/-! Semantic certificates for the rules of the primitive connectives and quantifiers.
The kernel has no such term constructors; it defines the connectives as constants and derives
these rules as theorems. The rules are validity-preserving for the primitive constructors. -/
namespace QEDFV.HOL

variable {κ : TyConVal} {S : Signature} {Γ : List Ty} {a b : Ty}

theorem valid_truth (I : ConstVal κ S) :
    Valid I ({ hyps := [], concl := (Term.truth : Term S Γ .bool) } : Sequent S Γ) := by
  intro ρ hρ η _
  trivial

theorem valid_falsity_elim (I : ConstVal κ S) (A : Sequent S Γ) (q : Term S Γ .bool)
    (hA : A.concl = Term.falsity) (hValid : Valid I A) :
    Valid I { hyps := A.hyps, concl := q } := by
  intro ρ hρ η hh
  have := hValid ρ hρ η hh
  rw [hA] at this
  exact this.elim

theorem valid_conj_intro (I : ConstVal κ S) (A B : Sequent S Γ) (p q : Term S Γ .bool)
    (hA : A.concl = p) (hB : B.concl = q) (hVA : Valid I A) (hVB : Valid I B) :
    Valid I { hyps := union A.hyps B.hyps, concl := Term.conj p q } := by
  intro ρ hρ η hh
  refine ⟨?_, ?_⟩
  · have := hVA ρ hρ η fun h hm ↦ hh h (List.mem_append_left _ hm)
    rwa [hA] at this
  · have := hVB ρ hρ η fun h hm ↦ hh h (List.mem_append_right _ hm)
    rwa [hB] at this

theorem valid_conj_elim_left (I : ConstVal κ S) (A : Sequent S Γ) (p q : Term S Γ .bool)
    (hA : A.concl = Term.conj p q) (hV : Valid I A) :
    Valid I { hyps := A.hyps, concl := p } := by
  intro ρ hρ η hh
  have := hV ρ hρ η hh
  rw [hA] at this
  exact this.1

theorem valid_conj_elim_right (I : ConstVal κ S) (A : Sequent S Γ) (p q : Term S Γ .bool)
    (hA : A.concl = Term.conj p q) (hV : Valid I A) :
    Valid I { hyps := A.hyps, concl := q } := by
  intro ρ hρ η hh
  have := hV ρ hρ η hh
  rw [hA] at this
  exact this.2

open Classical in
theorem valid_imp_intro (I : ConstVal κ S) (A : Sequent S Γ) (p : Term S Γ .bool)
    (hV : Valid I A) :
    Valid I { hyps := remove A.hyps p, concl := Term.imp p A.concl } := by
  intro ρ hρ η hh hp
  apply hV ρ hρ η
  intro h hm
  by_cases e : h = p
  · subst e; exact hp
  · exact hh h (mem_remove_of_mem_ne hm e)

theorem valid_imp_elim (I : ConstVal κ S) (A B : Sequent S Γ) (p q : Term S Γ .bool)
    (hA : A.concl = Term.imp p q) (hB : B.concl = p) (hVA : Valid I A) (hVB : Valid I B) :
    Valid I { hyps := union A.hyps B.hyps, concl := q } := by
  intro ρ hρ η hh
  have h1 := hVA ρ hρ η fun h hm ↦ hh h (List.mem_append_left _ hm)
  have h2 := hVB ρ hρ η fun h hm ↦ hh h (List.mem_append_right _ hm)
  rw [hA] at h1
  rw [hB] at h2
  exact h1 h2

theorem valid_all_intro (I : ConstVal κ S) (A : Sequent S Γ) (φ : Term S (a :: Γ) .bool)
    (hV : Valid I { hyps := (weakenSequent (b := a) A).hyps, concl := φ }) :
    Valid I { hyps := A.hyps, concl := Term.all φ } := by
  intro ρ hρ η hh x
  apply hV ρ hρ (Env.extend η x)
  intro h hm
  rcases List.mem_map.mp hm with ⟨h0, h0mem, rfl⟩
  simpa [weakenTerm, Term.eval_rename] using hh h0 h0mem

theorem valid_all_elim (I : ConstVal κ S) (A : Sequent S Γ) (φ : Term S (a :: Γ) .bool)
    (t : Term S Γ a) (hA : A.concl = Term.all φ) (hV : Valid I A) :
    Valid I { hyps := A.hyps, concl := φ.substitute (Sub.single t) } := by
  intro ρ hρ η hh
  have := hV ρ hρ η hh
  rw [hA] at this
  change (φ.substitute (Sub.single t)).eval I ρ hρ η
  rw [Term.eval_substitute, Sub.eval_single]
  exact this _

theorem valid_ex_intro (I : ConstVal κ S) (A : Sequent S Γ) (φ : Term S (a :: Γ) .bool)
    (t : Term S Γ a) (hA : A.concl = φ.substitute (Sub.single t)) (hV : Valid I A) :
    Valid I { hyps := A.hyps, concl := Term.ex φ } := by
  intro ρ hρ η hh
  have := hV ρ hρ η hh
  rw [hA, Term.eval_substitute, Sub.eval_single] at this
  exact ⟨_, this⟩

theorem valid_ex_elim (I : ConstVal κ S) (A B : Sequent S Γ) (φ : Term S (a :: Γ) .bool)
    (hA : A.concl = Term.ex φ)
    (hVA : Valid I A)
    (hVB : Valid I { hyps := φ :: (weakenSequent (b := a) B).hyps,
                     concl := weakenTerm B.concl }) :
    Valid I { hyps := union A.hyps B.hyps, concl := B.concl } := by
  intro ρ hρ η hh
  have h1 := hVA ρ hρ η fun h hm ↦ hh h (List.mem_append_left _ hm)
  rw [hA] at h1
  obtain ⟨x, hx⟩ := h1
  have := hVB ρ hρ (Env.extend η x) (by
    intro h hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hx
    · rcases List.mem_map.mp hm with ⟨h0, h0mem, rfl⟩
      simpa [weakenTerm, Term.eval_rename] using
        hh h0 (List.mem_append_right _ h0mem))
  simpa [weakenTerm, weakenSequent, Term.eval_rename] using this

theorem valid_classical (I : ConstVal κ S) (A : Sequent S Γ) (p : Term S Γ .bool)
    (hA : A.concl = Term.imp (Term.imp p Term.falsity) Term.falsity) (hV : Valid I A) :
    Valid I { hyps := A.hyps, concl := p } := by
  intro ρ hρ η hh
  have := hV ρ hρ η hh
  rw [hA] at this
  by_contra hn
  exact this (fun hp ↦ hn hp)

/-- Hilbert choice from a witness derived under hypotheses: the form of the select axiom
`P w ⟹ P (ε P)` that does not require a hypothesis-free witness. -/
theorem valid_choose_hyp (I : ConstVal κ S) (A : Sequent S Γ) (p : Term S (a :: Γ) .bool)
    (w : Term S Γ a) (hA : A.concl = p.substitute (Sub.single w)) (hV : Valid I A) :
    Valid I { hyps := A.hyps,
              concl := p.substitute (Sub.single (Term.choice.app (Term.lam p))) } := by
  intro ρ hρ η hh
  have hw := hV ρ hρ η hh
  rw [hA] at hw
  rw [Term.eval_substitute, Sub.eval_single]
  rw [Term.eval_substitute, Sub.eval_single] at hw
  letI : Nonempty (Ty.denote κ ρ a) := a.carrier_nonempty κ ρ hρ
  change p.eval I ρ hρ
    (Env.extend η ((Term.choice.app (Term.lam p)).eval I ρ hρ η))
  change p.eval I ρ hρ
    (Env.extend η
      (select (Ty.denote κ ρ a)
        (fun q ↦ p.eval I ρ hρ (Env.extend η q))))
  exact select_spec (Ty.denote κ ρ a)
    (fun q ↦ p.eval I ρ hρ (Env.extend η q))
    ⟨w.eval I ρ hρ η, hw⟩

end QEDFV.HOL
