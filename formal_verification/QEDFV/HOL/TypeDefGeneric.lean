import QEDFV.HOL.TypeDefinitions

/-! Carrier-level layer of a type definition, independent of syntax. For a type `E` and a
predicate `P` on it, `SubCarrier E P` is the subtype `{x // P x}` when `P` has a witness and
`PUnit` otherwise. The `PUnit` branch keeps every constructor carrier nonempty, so no model
is ever empty; the three type-definition laws hold on the subtype branch. -/
namespace QEDFV.HOL

section Generic

variable {E : Type} {P : E → Prop}

open Classical in
/-- The carrier of a defined type: the predicate subtype if the predicate has a witness,
`PUnit` otherwise. -/
noncomputable def SubCarrier (E : Type) (P : E → Prop) : Type :=
  if _ : ∃ x, P x then Subtype P else PUnit.{1}

theorem SubCarrier.eq_subtype (h : ∃ x, P x) : SubCarrier E P = Subtype P := dif_pos h

theorem SubCarrier.eq_punit (h : ¬ ∃ x, P x) : SubCarrier E P = PUnit.{1} := dif_neg h

theorem SubCarrier.nonempty (E : Type) (P : E → Prop) : Nonempty (SubCarrier E P) := by
  by_cases h : ∃ x, P x
  · rw [SubCarrier.eq_subtype h]
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, hx⟩⟩
  · rw [SubCarrier.eq_punit h]
    exact ⟨PUnit.unit⟩

theorem SubCarrier.subsingleton (h : ¬ ∃ x, P x) : Subsingleton (SubCarrier E P) := by
  rw [SubCarrier.eq_punit h]
  infer_instance

open Classical in
/-- `Rep`: the underlying element on the subtype branch, a default element otherwise. -/
noncomputable def SubCarrier.rep (P : E → Prop) (d : E) (x : SubCarrier E P) : E :=
  if h : ∃ x, P x then (cast (SubCarrier.eq_subtype h) x).1 else d

open Classical in
/-- `Abs`: a representation satisfying the predicate is kept, any other element is sent to a
fixed witness (as in `PredicateWitness.abs`). -/
noncomputable def SubCarrier.abs (P : E → Prop) (e : E) : SubCarrier E P :=
  if h : ∃ x, P x then cast (SubCarrier.eq_subtype h).symm ((⟨h⟩ : PredicateWitness E P).abs e)
  else cast (SubCarrier.eq_punit h).symm PUnit.unit

theorem SubCarrier.abs_rep (d : E) (x : SubCarrier E P) :
    SubCarrier.abs P (SubCarrier.rep P d x) = x := by
  by_cases h : ∃ x, P x
  · unfold SubCarrier.abs SubCarrier.rep
    simp only [dif_pos h]
    have := (⟨h⟩ : PredicateWitness E P).abs_rep (cast (SubCarrier.eq_subtype h) x)
    change cast (SubCarrier.eq_subtype h).symm ((⟨h⟩ : PredicateWitness E P).abs
      (cast (SubCarrier.eq_subtype h) x).1) = x
    have h2 : (⟨h⟩ : PredicateWitness E P).abs (cast (SubCarrier.eq_subtype h) x).1 =
        cast (SubCarrier.eq_subtype h) x := this
    rw [h2]
    exact cast_cast _ _ _ |>.trans (cast_eq _ _)
  · haveI := SubCarrier.subsingleton h
    exact Subsingleton.elim _ _

theorem SubCarrier.pred_rep (h : ∃ x, P x) (d : E) (x : SubCarrier E P) :
    P (SubCarrier.rep P d x) := by
  unfold SubCarrier.rep
  simp only [dif_pos h]
  exact (cast (SubCarrier.eq_subtype h) x).2

theorem SubCarrier.rep_abs (d : E) {e : E} (he : P e) :
    SubCarrier.rep P d (SubCarrier.abs P e) = e := by
  have h : ∃ x, P x := ⟨e, he⟩
  unfold SubCarrier.abs SubCarrier.rep
  simp only [dif_pos h]
  rw [cast_cast, cast_eq]
  exact (⟨h⟩ : PredicateWitness E P).rep_abs_of_pred he

/-- On the subtype branch `rep` is the projection of `PredicateWitness.rep`. -/
theorem SubCarrier.rep_eq_witness (h : ∃ x, P x) (d : E) (x : SubCarrier E P) :
    SubCarrier.rep P d x = (⟨h⟩ : PredicateWitness E P).rep (cast (SubCarrier.eq_subtype h) x) := by
  unfold SubCarrier.rep
  rw [dif_pos h]
  rfl

/-- On the subtype branch `abs` is `PredicateWitness.abs`. -/
theorem SubCarrier.abs_eq_witness (h : ∃ x, P x) (e : E) :
    cast (SubCarrier.eq_subtype h) (SubCarrier.abs P e) = (⟨h⟩ : PredicateWitness E P).abs e := by
  unfold SubCarrier.abs
  rw [dif_pos h, cast_cast, cast_eq]

end Generic

section Layer

variable {T E0 E1 : Type} {P0 : E0 → Prop} {P1 : E1 → Prop}

/-- `Rep` at a layer: the carrier `T` is identified with `SubCarrier E0 P0` and the
representation type `E0` with `E1` by (propositional) equalities. -/
noncomputable def layerRep (hT : T = SubCarrier E0 P0) (e : E0 = E1) (d : E1) : T → E1 :=
  fun x ↦ cast e (SubCarrier.rep P0 (cast e.symm d) (cast hT x))

/-- `Abs` at a layer. -/
noncomputable def layerAbs (hT : T = SubCarrier E0 P0) (e : E0 = E1) : E1 → T :=
  fun y ↦ cast hT.symm (SubCarrier.abs P0 (cast e.symm y))

theorem layer_abs_rep (hT : T = SubCarrier E0 P0) (e : E0 = E1) (d : E1) (x : T) :
    layerAbs hT e (layerRep hT e d x) = x := by
  subst hT
  subst e
  simp only [layerRep, layerAbs, cast_eq]
  exact SubCarrier.abs_rep _ x

theorem layer_pred_rep (hT : T = SubCarrier E0 P0) (e : E0 = E1) (d : E1)
    (hP : ∀ x, P0 x ↔ P1 (cast e x)) (hw : ∃ x, P0 x) (x : T) :
    P1 (layerRep hT e d x) := by
  subst hT
  subst e
  simp only [layerRep, cast_eq]
  exact (hP _).mp (SubCarrier.pred_rep hw _ x)

theorem layer_rep_abs (hT : T = SubCarrier E0 P0) (e : E0 = E1) (d : E1)
    (hP : ∀ x, P0 x ↔ P1 (cast e x)) {y : E1} (hy : P1 y) :
    layerRep hT e d (layerAbs hT e y) = y := by
  subst hT
  subst e
  simp only [layerRep, layerAbs, cast_eq]
  exact SubCarrier.rep_abs _ ((hP _).mpr hy)

end Layer

end QEDFV.HOL
