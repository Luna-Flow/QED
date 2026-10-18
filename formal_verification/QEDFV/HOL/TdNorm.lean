import QEDFV.HOL.DerivedRules
import QEDFV.HOL.TdTypes
import QEDFV.HOL.TypeDefGate

/-! The retraction of the representation type onto the predicate of a type definition:
`norm y = ε z. (P y ⟹ z = y) ∧ P z`. Given a derivable witness, it satisfies
`⊢ P (norm y)`, `P y ⊢ norm y = y` and `⊢ norm (norm y) = norm y`. -/
namespace QEDFV.HOL

/-- The data of a retraction: a representation type and a closed predicate on it. -/
structure NormCfg (S : Signature) where
  R : Ty
  P : Term S [] (.arr R .bool)

namespace NormCfg

variable {S : Signature} (C : NormCfg S) {Γ : List Ty} {es : List (ModelExtension S)}

/-- The predicate in an arbitrary context. -/
def predIn (Γ : List Ty) : Term S Γ (.arr C.R .bool) :=
  C.P.rename (fun {_} v ↦ by cases v)

theorem predIn_eq (Γ : List Ty) : C.predIn Γ = (C.P.closedLift : Term S Γ (.arr C.R .bool)) := by
  unfold predIn Term.closedLift
  exact congrArg (fun r ↦ C.P.rename r) (Ren.empty_ext _ _)

/-- `P t`. -/
def holds' (t : Term S Γ C.R) : Term S Γ .bool := (C.predIn Γ).app t

/-- The body of the selection predicate for `y := t`: `(P t ⟹ z = t) ∧ P z`, in the context
extended by `z`. -/
def normBody (t : Term S Γ C.R) : Term S (C.R :: Γ) .bool :=
  Term.conj (Term.imp (C.holds' (t.rename Var.succ)) ((Term.var .zero).equal (t.rename Var.succ)))
    (C.holds' (Term.var .zero))

/-- `ε z. (P t ⟹ z = t) ∧ P z`. -/
def normSel (t : Term S Γ C.R) : Term S Γ C.R :=
  Term.choice.app (Term.lam (C.normBody t))

/-- The retraction as a term. -/
def normIn (Γ : List Ty) : Term S Γ (.arr C.R C.R) :=
  Term.lam (C.normSel (Term.var .zero))

/-- `norm t`. -/
def nrm (t : Term S Γ C.R) : Term S Γ C.R := (C.normIn Γ).app t

theorem predIn_substitute {Δ : List Ty} (σ : Sub S Γ Δ) :
    (C.predIn Γ).substitute σ = C.predIn Δ := by
  rw [predIn_eq, predIn_eq]
  exact Term.closedLift_substitute _ _

theorem normBody_substitute {Δ : List Ty} (t : Term S Γ C.R) (σ : Sub S Γ Δ) :
    (C.normBody t).substitute (Sub.lift σ) = C.normBody (t.substitute σ) := by
  have h1 : ((t.rename Var.succ).substitute (Sub.lift σ) : Term S (C.R :: Δ) C.R)
      = (t.substitute σ).rename Var.succ := by
    rw [Term.substitute_rename, Term.rename_substitute]
    rfl
  simp only [normBody, holds', Term.substitute, predIn_substitute, h1]
  rfl

theorem normSel_substitute {Δ : List Ty} (t : Term S Γ C.R) (σ : Sub S Γ Δ) :
    (C.normSel t).substitute σ = C.normSel (t.substitute σ) := by
  simp only [normSel, Term.substitute, normBody_substitute]

theorem rename_succ_substitute_single {b : Ty} (t : Term S Γ b) (u : Term S Γ a) :
    (t.rename Var.succ).substitute (Sub.single u) = t := by
  rw [Term.substitute_rename]
  have : @Eq (Sub S Γ Γ) (fun v ↦ Sub.single u (Var.succ v)) (fun v ↦ Term.var v) := rfl
  rw [this]
  have := Term.substitute_var t (fun v ↦ v)
  rw [Term.rename_id] at this
  exact this

theorem nrm_beta (t : Term S Γ C.R) :
    HistoryDerivation S es { hyps := [], concl := (C.nrm t).equal (C.normSel t) } := by
  have := HistoryDerivation.core (es := es)
    (Derivation.beta (C.normSel (Term.var Var.zero)) t)
  rw [C.normSel_substitute] at this
  exact this

theorem normBody_single (t u : Term S Γ C.R) :
    (C.normBody t).substitute (Sub.single u)
      = Term.conj (Term.imp (C.holds' t) (u.equal t)) (C.holds' u) := by
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
theorem normSel_spec {w : Term S [] C.R}
    (hw : HistoryDerivation S es { hyps := [], concl := C.P.app w }) (t : Term S Γ C.R) :
    HistoryDerivation S es
      ({ hyps := [], concl := Term.conj (Term.imp (C.holds' t) ((C.normSel t).equal t))
          (C.holds' (C.normSel t)) } : Sequent S Γ) := by
  have hwΓ : HistoryDerivation S es
      ({ hyps := [], concl := C.holds' (w.closedLift : Term S Γ C.R) } : Sequent S Γ) := by
    have := closedLift_derivable (Γ := Γ) hw
    rw [holds', predIn_eq]
    exact this
  -- case P t
  have c1 : HistoryDerivation S es
      ({ hyps := [C.holds' t], concl := Term.conj (Term.imp (C.holds' t) ((C.normSel t).equal t))
          (C.holds' (C.normSel t)) } : Sequent S Γ) := by
    have hA : HistoryDerivation S es
        ({ hyps := [C.holds' t], concl := (C.normBody t).substitute (Sub.single t) } :
          Sequent S Γ) := by
      rw [normBody_single]
      exact HistoryDerivation.conjI (HistoryDerivation.impI (HistoryDerivation.refl' t))
        (HistoryDerivation.assume' _ (by simp))
    refine HistoryDerivation.of_eq ?_ (HistoryDerivation.chooseHyp (es := es)
      (A := { hyps := [C.holds' t], concl := (C.normBody t).substitute (Sub.single t) })
      (C.normBody t) t rfl hA)
    simp only []
    rw [normBody_single]
    rfl
  -- case ¬P t
  have c2 : HistoryDerivation S es
      ({ hyps := [Term.imp (C.holds' t) Term.falsity],
         concl := Term.conj (Term.imp (C.holds' t) ((C.normSel t).equal t))
          (C.holds' (C.normSel t)) } : Sequent S Γ) := by
    have hA : HistoryDerivation S es
        ({ hyps := [Term.imp (C.holds' t) Term.falsity],
           concl := (C.normBody t).substitute (Sub.single (w.closedLift)) } : Sequent S Γ) := by
      rw [normBody_single]
      refine HistoryDerivation.conjI (HistoryDerivation.impI ?_) (hwΓ.mono (by simp))
      refine HistoryDerivation.exFalso (HistoryDerivation.mp (p := C.holds' t) ?_ ?_)
      · exact HistoryDerivation.assume' _ (by simp)
      · exact HistoryDerivation.assume' _ (by simp)
    refine HistoryDerivation.of_eq ?_ (HistoryDerivation.chooseHyp (es := es)
      (A := { hyps := [Term.imp (C.holds' t) Term.falsity],
              concl := (C.normBody t).substitute (Sub.single (w.closedLift)) })
      (C.normBody t) w.closedLift rfl hA)
    simp only []
    rw [normBody_single]
    rfl
  exact HistoryDerivation.byCases (C.holds' t) (L := [])
    (c1.mono (fun h hh ↦ by simpa using hh)) (c2.mono (fun h hh ↦ by simpa using hh))

/-- `⊢ P (norm t)`. -/
theorem nrm_range {w : Term S [] C.R}
    (hw : HistoryDerivation S es { hyps := [], concl := C.P.app w }) (t : Term S Γ C.R) :
    HistoryDerivation S es { hyps := [], concl := C.holds' (C.nrm t) } := by
  have h1 := HistoryDerivation.conjR (C.normSel_spec hw t)
  have h2 : HistoryDerivation S es
      { hyps := [], concl := (C.holds' (C.nrm t)).equal (C.holds' (C.normSel t)) } :=
    HistoryDerivation.mkComb' (HistoryDerivation.refl' _) (C.nrm_beta t)
  exact HistoryDerivation.eqMp' (HistoryDerivation.sym h2) h1

/-- `P t ⊢ norm t = t`. -/
theorem nrm_fix {w : Term S [] C.R}
    (hw : HistoryDerivation S es { hyps := [], concl := C.P.app w }) (t : Term S Γ C.R) :
    HistoryDerivation S es { hyps := [C.holds' t], concl := (C.nrm t).equal t } := by
  have h1 := HistoryDerivation.conjL (C.normSel_spec hw t)
  have h2 : HistoryDerivation S es
      { hyps := [C.holds' t], concl := (C.normSel t).equal t } :=
    HistoryDerivation.mp (h1.mono (fun h hh ↦ by simp at hh))
      (HistoryDerivation.assume' _ (by simp))
  exact HistoryDerivation.trans' ((C.nrm_beta t).mono (fun h hh ↦ by simp at hh)) h2

/-- `⊢ norm (norm t) = norm t`. -/
theorem nrm_idem {w : Term S [] C.R}
    (hw : HistoryDerivation S es { hyps := [], concl := C.P.app w }) (t : Term S Γ C.R) :
    HistoryDerivation S es { hyps := [], concl := (C.nrm (C.nrm t)).equal (C.nrm t) } :=
  HistoryDerivation.cut (C.nrm_range hw t) (C.nrm_fix hw (C.nrm t))

theorem predIn_rename {Δ : List Ty} (r : Ren Γ Δ) : (C.predIn Γ).rename r = C.predIn Δ := by
  rw [predIn_eq, predIn_eq]
  exact Term.closedLift_rename _ _

theorem normBody_rename {Δ : List Ty} (t : Term S Γ C.R) (r : Ren Γ Δ) :
    (C.normBody t).rename (Ren.lift r) = C.normBody (t.rename r) := by
  have h1 : ((t.rename Var.succ).rename (Ren.lift r) : Term S (C.R :: Δ) C.R)
      = (t.rename r).rename Var.succ := by
    rw [Term.rename_rename, Term.rename_rename]
    rfl
  simp only [normBody, holds', Term.rename, predIn_rename, h1]
  rfl

theorem normSel_rename {Δ : List Ty} (t : Term S Γ C.R) (r : Ren Γ Δ) :
    (C.normSel t).rename r = C.normSel (t.rename r) := by
  simp only [normSel, Term.rename, normBody_rename]

theorem normIn_rename {Δ : List Ty} (r : Ren Γ Δ) : (C.normIn Γ).rename r = C.normIn Δ := by
  simp only [normIn, Term.rename, normSel_rename]
  rfl

theorem normIn_eq (Γ : List Ty) :
    C.normIn Γ = ((C.normIn [] : Term S [] (.arr C.R C.R)).closedLift : Term S Γ (.arr C.R C.R)) :=
  (C.normIn_rename Ren.empty).symm

end NormCfg

end QEDFV.HOL
