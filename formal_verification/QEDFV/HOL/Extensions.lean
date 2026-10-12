import QEDFV.HOL.Types
import QEDFV.HOL.Evaluation

/-! Semantic extension witnesses. These are the carrier-level contracts required by
typedef and choice gates; they are independent of the executable MoonBit gate. -/
namespace QEDFV.HOL

variable {κ : TyConVal}

structure PredicateWitness (α : Type) (P : α → Prop) where
  witness : ∃ x, P x

noncomputable def PredicateWitness.abs
    {α : Type} {P : α → Prop} (w : PredicateWitness α P) (x : α) :
    Subtype P := by
  classical
  exact if h : P x then ⟨x, h⟩ else ⟨Classical.choose w.witness, Classical.choose_spec w.witness⟩

def PredicateWitness.rep {α : Type} {P : α → Prop} (_w : PredicateWitness α P)
    (x : Subtype P) : α := x.1

theorem PredicateWitness.abs_rep
    {α : Type} {P : α → Prop} (w : PredicateWitness α P) (x : Subtype P) :
    w.abs (w.rep x) = x := by
  classical
  apply Subtype.ext
  simp [PredicateWitness.abs, PredicateWitness.rep, x.property]

theorem PredicateWitness.rep_abs_of_pred
    {α : Type} {P : α → Prop} (w : PredicateWitness α P) {x : α} (hx : P x) :
    w.rep (w.abs x) = x := by
  classical
  simp [PredicateWitness.abs, PredicateWitness.rep, hx]

theorem PredicateWitness.carrier_nonempty
    {α : Type} {P : α → Prop} (w : PredicateWitness α P) :
    Nonempty (Subtype P) := by
  exact ⟨w.abs (Classical.choose w.witness)⟩

noncomputable def chooseFromWitness {α : Type} [Nonempty α]
    (P : α → Prop) (_w : ∃ x, P x) : α :=
  by
    classical
    exact if h : ∃ x, P x then Classical.choose h else Classical.choice inferInstance

theorem chooseFromWitness_spec {α : Type} [Nonempty α]
    (P : α → Prop) (w : ∃ x, P x) : P (chooseFromWitness P w) := by
  simp only [chooseFromWitness, dif_pos w]
  exact Classical.choose_spec w

end QEDFV.HOL
