import QEDFV.HOL.DerivedRules
import QEDFV.HOL.TdTypes
import QEDFV.HOL.TypeDefGate

/-! The retraction of the representation type onto the predicate of a type definition:
`norm y = ε z. (P y ⟹ z = y) ∧ P z`. Given a derivable witness, it satisfies
`⊢ P (norm y)`, `P y ⊢ norm y = y` and `⊢ norm (norm y) = norm y`. -/
namespace QEDFV.HOL

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S) {Γ : List Ty} {es : List (ModelExtension S)}

theorem predIn_eq (Γ : List Ty) : G.predIn Γ = (G.pred.closedLift : Term S Γ (.arr G.repTy .bool)) := by
  unfold predIn Term.closedLift
  exact congrArg (fun r ↦ G.pred.rename r) (Ren.empty_ext _ _)

/-- `P t`. -/
def holds' (t : Term S Γ G.repTy) : Term S Γ .bool := (G.predIn Γ).app t

/-- The body of the selection predicate for `y := t`: `(P t ⟹ z = t) ∧ P z`, in the context
extended by `z`. -/
def normBody (t : Term S Γ G.repTy) : Term S (G.repTy :: Γ) .bool :=
  Term.conj (Term.imp (G.holds' (t.rename Var.succ)) ((Term.var .zero).equal (t.rename Var.succ)))
    (G.holds' (Term.var .zero))

/-- `ε z. (P t ⟹ z = t) ∧ P z`. -/
def normSel (t : Term S Γ G.repTy) : Term S Γ G.repTy :=
  Term.choice.app (Term.lam (G.normBody t))

/-- The retraction as a term. -/
def normIn (Γ : List Ty) : Term S Γ (.arr G.repTy G.repTy) :=
  Term.lam (G.normSel (Term.var .zero))

/-- `norm t`. -/
def nrm (t : Term S Γ G.repTy) : Term S Γ G.repTy := (G.normIn Γ).app t

theorem predIn_substitute {Δ : List Ty} (σ : Sub S Γ Δ) :
    (G.predIn Γ).substitute σ = G.predIn Δ := by
  rw [predIn_eq, predIn_eq]
  exact Term.closedLift_substitute _ _

theorem normBody_substitute {Δ : List Ty} (t : Term S Γ G.repTy) (σ : Sub S Γ Δ) :
    (G.normBody t).substitute (Sub.lift σ) = G.normBody (t.substitute σ) := by
  have h1 : ((t.rename Var.succ).substitute (Sub.lift σ) : Term S (G.repTy :: Δ) G.repTy)
      = (t.substitute σ).rename Var.succ := by
    rw [Term.substitute_rename, Term.rename_substitute]
    rfl
  simp only [normBody, holds', Term.substitute, predIn_substitute, h1]
  rfl

theorem normSel_substitute {Δ : List Ty} (t : Term S Γ G.repTy) (σ : Sub S Γ Δ) :
    (G.normSel t).substitute σ = G.normSel (t.substitute σ) := by
  simp only [normSel, Term.substitute, normBody_substitute]

theorem rename_succ_substitute_single {b : Ty} (t : Term S Γ b) (u : Term S Γ a) :
    (t.rename Var.succ).substitute (Sub.single u) = t := by
  rw [Term.substitute_rename]
  have : @Eq (Sub S Γ Γ) (fun v ↦ Sub.single u (Var.succ v)) (fun v ↦ Term.var v) := rfl
  rw [this]
  have := Term.substitute_var t (fun v ↦ v)
  rw [Term.rename_id] at this
  exact this

theorem nrm_beta (t : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := [], concl := (G.nrm t).equal (G.normSel t) } := by
  have := HistoryDerivation.core (es := es)
    (Derivation.beta (G.normSel (Term.var Var.zero)) t)
  rw [G.normSel_substitute] at this
  exact this

theorem normBody_single (t u : Term S Γ G.repTy) :
    (G.normBody t).substitute (Sub.single u)
      = Term.conj (Term.imp (G.holds' t) (u.equal t)) (G.holds' u) := by
  simp only [normBody, holds', Term.substitute, predIn_substitute, rename_succ_substitute_single]
  rfl

theorem closedLift_derivable {c : Term S [] .bool}
    (d : HistoryDerivation S es { hyps := [], concl := c }) :
    HistoryDerivation S es
      ({ hyps := [], concl := (c.closedLift : Term S Γ .bool) } : Sequent S Γ) := by
  have := HistoryDerivation.instTerm (Δ := Γ) (fun {_} v ↦ Term.var (Ren.empty v)) d
  refine HistoryDerivation.of_eq ?_ this
  simp only [termSubstSequent, List.map_nil]
  congr 1
  unfold Term.closedLift
  exact Term.substitute_var c _

/-- The selection property of the retraction. -/
theorem normSel_spec {w : Term S [] G.repTy}
    (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) (t : Term S Γ G.repTy) :
    HistoryDerivation S es
      ({ hyps := [], concl := Term.conj (Term.imp (G.holds' t) ((G.normSel t).equal t))
          (G.holds' (G.normSel t)) } : Sequent S Γ) := by
  have hwΓ : HistoryDerivation S es
      ({ hyps := [], concl := G.holds' (w.closedLift : Term S Γ G.repTy) } : Sequent S Γ) := by
    have := closedLift_derivable (Γ := Γ) hw
    rw [holds', predIn_eq]
    exact this
  -- case P t
  have c1 : HistoryDerivation S es
      ({ hyps := [G.holds' t], concl := Term.conj (Term.imp (G.holds' t) ((G.normSel t).equal t))
          (G.holds' (G.normSel t)) } : Sequent S Γ) := by
    have hA : HistoryDerivation S es
        ({ hyps := [G.holds' t], concl := (G.normBody t).substitute (Sub.single t) } :
          Sequent S Γ) := by
      rw [normBody_single]
      exact HistoryDerivation.conjI (HistoryDerivation.impI (HistoryDerivation.refl' t))
        (HistoryDerivation.assume' _ (by simp))
    refine HistoryDerivation.of_eq ?_ (HistoryDerivation.chooseHyp (es := es)
      (A := { hyps := [G.holds' t], concl := (G.normBody t).substitute (Sub.single t) })
      (G.normBody t) t rfl hA)
    simp only []
    rw [normBody_single]
    rfl
  -- case ¬P t
  have c2 : HistoryDerivation S es
      ({ hyps := [Term.imp (G.holds' t) Term.falsity],
         concl := Term.conj (Term.imp (G.holds' t) ((G.normSel t).equal t))
          (G.holds' (G.normSel t)) } : Sequent S Γ) := by
    have hA : HistoryDerivation S es
        ({ hyps := [Term.imp (G.holds' t) Term.falsity],
           concl := (G.normBody t).substitute (Sub.single (w.closedLift)) } : Sequent S Γ) := by
      rw [normBody_single]
      refine HistoryDerivation.conjI (HistoryDerivation.impI ?_) (hwΓ.mono (by simp))
      refine HistoryDerivation.exFalso (HistoryDerivation.mp (p := G.holds' t) ?_ ?_)
      · exact HistoryDerivation.assume' _ (by simp)
      · exact HistoryDerivation.assume' _ (by simp)
    refine HistoryDerivation.of_eq ?_ (HistoryDerivation.chooseHyp (es := es)
      (A := { hyps := [Term.imp (G.holds' t) Term.falsity],
              concl := (G.normBody t).substitute (Sub.single (w.closedLift)) })
      (G.normBody t) w.closedLift rfl hA)
    simp only []
    rw [normBody_single]
    rfl
  exact HistoryDerivation.byCases (G.holds' t) (L := [])
    (c1.mono (fun h hh ↦ by simpa using hh)) (c2.mono (fun h hh ↦ by simpa using hh))

/-- `⊢ P (norm t)`. -/
theorem nrm_range {w : Term S [] G.repTy}
    (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) (t : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := [], concl := G.holds' (G.nrm t) } := by
  have h1 := HistoryDerivation.conjR (G.normSel_spec hw t)
  have h2 : HistoryDerivation S es
      { hyps := [], concl := (G.holds' (G.nrm t)).equal (G.holds' (G.normSel t)) } :=
    HistoryDerivation.mkComb' (HistoryDerivation.refl' _) (G.nrm_beta t)
  exact HistoryDerivation.eqMp' (HistoryDerivation.sym h2) h1

/-- `P t ⊢ norm t = t`. -/
theorem nrm_fix {w : Term S [] G.repTy}
    (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) (t : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := [G.holds' t], concl := (G.nrm t).equal t } := by
  have h1 := HistoryDerivation.conjL (G.normSel_spec hw t)
  have h2 : HistoryDerivation S es
      { hyps := [G.holds' t], concl := (G.normSel t).equal t } :=
    HistoryDerivation.mp (h1.mono (fun h hh ↦ by simp at hh))
      (HistoryDerivation.assume' _ (by simp))
  exact HistoryDerivation.trans' ((G.nrm_beta t).mono (fun h hh ↦ by simp at hh)) h2

/-- `⊢ norm (norm t) = norm t`. -/
theorem nrm_idem {w : Term S [] G.repTy}
    (hw : HistoryDerivation S es { hyps := [], concl := G.pred.app w }) (t : Term S Γ G.repTy) :
    HistoryDerivation S es { hyps := [], concl := (G.nrm (G.nrm t)).equal (G.nrm t) } :=
  HistoryDerivation.cut (G.nrm_range hw t) (G.nrm_fix hw (G.nrm t))

end TypeDefGate

end QEDFV.HOL
