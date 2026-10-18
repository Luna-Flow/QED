import QEDFV.HOL.Unfold

/-! Derived natural-deduction combinators for `HistoryDerivation`, stated for sequents with
hypotheses as sets (`weakenHyps`). They are used to build the derivations of the normalisation
lemmas in the typedef-erasure development. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ : List Ty} {a b : Ty} {es : List (ModelExtension S)}

namespace HistoryDerivation

/-- Hypotheses can be any list containing the needed ones. -/
theorem mono {A : Sequent S Γ} {L : List (Term S Γ .bool)} (d : HistoryDerivation S es A)
    (hL : ∀ h, h ∈ A.hyps → h ∈ L) :
    HistoryDerivation S es { hyps := L, concl := A.concl } :=
  .weakenHyps L hL d

/-- Assumption. -/
theorem assume' (p : Term S Γ .bool) {L : List (Term S Γ .bool)} (h : p ∈ L) :
    HistoryDerivation S es { hyps := L, concl := p } :=
  (HistoryDerivation.core (.assume p)).mono (fun x hx ↦ by
    simp only [List.mem_singleton] at hx; rw [hx]; exact h)

/-- Implication introduction with set-like hypotheses. -/
theorem impI {p q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d : HistoryDerivation S es { hyps := p :: L, concl := q }) :
    HistoryDerivation S es { hyps := L, concl := Term.imp p q } := by
  have := HistoryDerivation.impIntro (A := { hyps := p :: L, concl := q }) p d
  refine (this.mono ?_)
  intro h hh
  classical
  simp only [remove, List.mem_filter] at hh
  obtain ⟨hh1, hh2⟩ := hh
  rcases List.mem_cons.mp hh1 with rfl | hm
  · simp at hh2
  · exact hm

/-- Modus ponens. -/
theorem mp {p q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d1 : HistoryDerivation S es { hyps := L, concl := Term.imp p q })
    (d2 : HistoryDerivation S es { hyps := L, concl := p }) :
    HistoryDerivation S es { hyps := L, concl := q } := by
  have := HistoryDerivation.impElim (A := { hyps := L, concl := Term.imp p q })
    (B := { hyps := L, concl := p }) rfl rfl d1 d2
  exact this.mono (fun h hh ↦ by
    simp only [union, List.mem_append] at hh; exact hh.elim id id)

/-- Cut: use a derived lemma as a hypothesis. -/
theorem cut {p q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d1 : HistoryDerivation S es { hyps := L, concl := p })
    (d2 : HistoryDerivation S es { hyps := p :: L, concl := q }) :
    HistoryDerivation S es { hyps := L, concl := q } :=
  mp (impI d2) d1

/-- Ex falso. -/
theorem exFalso {q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d : HistoryDerivation S es { hyps := L, concl := Term.falsity }) :
    HistoryDerivation S es { hyps := L, concl := q } :=
  HistoryDerivation.falsityElim (A := { hyps := L, concl := Term.falsity }) q rfl d

/-- Double negation elimination. -/
theorem dne {q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d : HistoryDerivation S es { hyps := Term.imp q Term.falsity :: L, concl := Term.falsity }) :
    HistoryDerivation S es { hyps := L, concl := q } :=
  HistoryDerivation.classical (A := { hyps := L, concl := Term.imp (Term.imp q Term.falsity) Term.falsity })
    rfl (impI d)

/-- Case analysis on a proposition (classical). -/
theorem byCases (p : Term S Γ .bool) {q : Term S Γ .bool} {L : List (Term S Γ .bool)}
    (d1 : HistoryDerivation S es { hyps := p :: L, concl := q })
    (d2 : HistoryDerivation S es { hyps := Term.imp p Term.falsity :: L, concl := q }) :
    HistoryDerivation S es { hyps := L, concl := q } := by
  refine dne ?_
  have hnq : HistoryDerivation S es
      { hyps := Term.imp q Term.falsity :: L, concl := Term.imp q Term.falsity } :=
    assume' _ (List.mem_cons_self ..)
  have hnp : HistoryDerivation S es
      { hyps := Term.imp q Term.falsity :: L, concl := Term.imp p Term.falsity } := by
    refine impI (mp (p := q) ?_ ?_)
    · exact hnq.mono (fun h hh ↦ by
        simp only [List.mem_cons] at hh ⊢
        tauto)
    · exact d1.mono (fun h hh ↦ by
        simp only [List.mem_cons] at hh ⊢
        tauto)
  have hq : HistoryDerivation S es
      { hyps := Term.imp q Term.falsity :: L, concl := q } :=
    cut hnp (d2.mono (fun h hh ↦ by
      simp only [List.mem_cons] at hh ⊢
      tauto))
  exact mp (p := q) hnq hq

/-- Reflexivity with arbitrary hypotheses. -/
theorem refl' {L : List (Term S Γ .bool)} (t : Term S Γ a) :
    HistoryDerivation S es { hyps := L, concl := t.equal t } :=
  (HistoryDerivation.core (.refl t)).mono (fun h hh ↦ by simp at hh)

/-- Transitivity of equality. -/
theorem trans' {L : List (Term S Γ .bool)} {x y z : Term S Γ a}
    (d1 : HistoryDerivation S es { hyps := L, concl := x.equal y })
    (d2 : HistoryDerivation S es { hyps := L, concl := y.equal z }) :
    HistoryDerivation S es { hyps := L, concl := x.equal z } :=
  (HistoryDerivation.trans (A := { hyps := L, concl := x.equal y })
    (B := { hyps := L, concl := y.equal z }) rfl rfl d1 d2).mono
    (fun h hh ↦ by simp only [union, List.mem_append] at hh; exact hh.elim id id)

/-- Congruence for application. -/
theorem mkComb' {L : List (Term S Γ .bool)} {f g : Term S Γ (.arr a b)} {x y : Term S Γ a}
    (d1 : HistoryDerivation S es { hyps := L, concl := f.equal g })
    (d2 : HistoryDerivation S es { hyps := L, concl := x.equal y }) :
    HistoryDerivation S es { hyps := L, concl := (f.app x).equal (g.app y) } :=
  (HistoryDerivation.mkComb (A := { hyps := L, concl := f.equal g })
    (B := { hyps := L, concl := x.equal y }) rfl rfl d1 d2).mono
    (fun h hh ↦ by simp only [union, List.mem_append] at hh; exact hh.elim id id)

/-- Equality is symmetric. -/
theorem sym {L : List (Term S Γ .bool)} {x y : Term S Γ a}
    (d : HistoryDerivation S es { hyps := L, concl := x.equal y }) :
    HistoryDerivation S es { hyps := L, concl := y.equal x } := by
  -- (=) x = (=) y, then ((=) x) x = ((=) y) x, i.e. (x = x) = (y = x)
  have h1 : HistoryDerivation S es
      { hyps := L, concl := ((Term.eq : Term S Γ (.arr a (.arr a .bool))).app x).equal
          ((Term.eq : Term S Γ (.arr a (.arr a .bool))).app y) } :=
    mkComb' (refl' _) d
  have h2 := mkComb' h1 (refl' (L := L) x)
  have h3 : HistoryDerivation S es { hyps := L, concl := x.equal x } := refl' x
  exact HistoryDerivation.eqMp (A := { hyps := L, concl := (x.equal x).equal (y.equal x) })
    (B := { hyps := L, concl := x.equal x }) rfl rfl h2 h3 |>.mono
    (fun h hh ↦ by simp only [union, List.mem_append] at hh; exact hh.elim id id)

/-- Rewriting a derived proposition along an equation. -/
theorem eqMp' {L : List (Term S Γ .bool)} {p q : Term S Γ .bool}
    (d1 : HistoryDerivation S es { hyps := L, concl := p.equal q })
    (d2 : HistoryDerivation S es { hyps := L, concl := p }) :
    HistoryDerivation S es { hyps := L, concl := q } :=
  (HistoryDerivation.eqMp (A := { hyps := L, concl := p.equal q })
    (B := { hyps := L, concl := p }) rfl rfl d1 d2).mono
    (fun h hh ↦ by simp only [union, List.mem_append] at hh; exact hh.elim id id)

/-- Conjunction introduction. -/
theorem conjI {L : List (Term S Γ .bool)} {p q : Term S Γ .bool}
    (d1 : HistoryDerivation S es { hyps := L, concl := p })
    (d2 : HistoryDerivation S es { hyps := L, concl := q }) :
    HistoryDerivation S es { hyps := L, concl := Term.conj p q } :=
  (HistoryDerivation.conjIntro (A := { hyps := L, concl := p })
    (B := { hyps := L, concl := q }) rfl rfl d1 d2).mono
    (fun h hh ↦ by simp only [union, List.mem_append] at hh; exact hh.elim id id)

theorem conjL {L : List (Term S Γ .bool)} {p q : Term S Γ .bool}
    (d : HistoryDerivation S es { hyps := L, concl := Term.conj p q }) :
    HistoryDerivation S es { hyps := L, concl := p } :=
  HistoryDerivation.conjElimLeft (A := { hyps := L, concl := Term.conj p q }) rfl d

theorem conjR {L : List (Term S Γ .bool)} {p q : Term S Γ .bool}
    (d : HistoryDerivation S es { hyps := L, concl := Term.conj p q }) :
    HistoryDerivation S es { hyps := L, concl := q } :=
  HistoryDerivation.conjElimRight (A := { hyps := L, concl := Term.conj p q }) rfl d

end HistoryDerivation

end QEDFV.HOL
