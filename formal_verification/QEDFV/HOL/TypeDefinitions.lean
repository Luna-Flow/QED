import QEDFV.HOL.Extensions

namespace QEDFV.HOL

/-! Parametric semantic content of a type-definition gate. The predicate and its
witness are quantified over every admissible interpretation of the declared
type variables. -/
structure PredicateFamily where
  repTy : Ty
  pred : (ρ : TypeVal) → Admissible ρ → Ty.denote ρ repTy → Prop
  witness : ∀ (ρ : TypeVal) (hρ : Admissible ρ), ∃ x, pred ρ hρ x

def PredicateFamily.witnessAt (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ) : PredicateWitness (Ty.denote ρ F.repTy) (F.pred ρ hρ) :=
  ⟨F.witness ρ hρ⟩

noncomputable def PredicateFamily.abs (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ) (x : Ty.denote ρ F.repTy) :
    {y : Ty.denote ρ F.repTy // F.pred ρ hρ y} :=
  (F.witnessAt ρ hρ).abs x

def PredicateFamily.rep (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ F.repTy // F.pred ρ hρ y}) : Ty.denote ρ F.repTy :=
  (F.witnessAt ρ hρ).rep x

theorem PredicateFamily.carrier_nonempty (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ) :
    Nonempty {y : Ty.denote ρ F.repTy // F.pred ρ hρ y} :=
  (F.witnessAt ρ hρ).carrier_nonempty

theorem PredicateFamily.abs_rep (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ F.repTy // F.pred ρ hρ y}) :
    F.abs ρ hρ (F.rep ρ hρ x) = x := by
  exact (F.witnessAt ρ hρ).abs_rep x

theorem PredicateFamily.rep_in_range (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ F.repTy // F.pred ρ hρ y}) :
    F.pred ρ hρ (F.rep ρ hρ x) :=
  x.property

theorem PredicateFamily.rep_abs_of_pred (F : PredicateFamily) (ρ : TypeVal)
    (hρ : Admissible ρ) {x : Ty.denote ρ F.repTy} (hx : F.pred ρ hρ x) :
    F.rep ρ hρ (F.abs ρ hρ x) = x := by
  exact (F.witnessAt ρ hρ).rep_abs_of_pred hx

structure TypeDefContract where
  family : PredicateFamily

noncomputable def TypeDefContract.abs (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ) (x : Ty.denote ρ C.family.repTy) :
    {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.family.abs ρ hρ x

def TypeDefContract.rep (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}) :
    Ty.denote ρ C.family.repTy :=
  C.family.rep ρ hρ x

theorem TypeDefContract.nonempty (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ) :
    Nonempty {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.family.carrier_nonempty ρ hρ

theorem TypeDefContract.abs_rep (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}) :
    C.abs ρ hρ (C.rep ρ hρ x) = x :=
  C.family.abs_rep ρ hρ x

theorem TypeDefContract.rep_in_range (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ)
    (x : {y : Ty.denote ρ C.family.repTy // C.family.pred ρ hρ y}) :
    C.family.pred ρ hρ (C.rep ρ hρ x) :=
  C.family.rep_in_range ρ hρ x

theorem TypeDefContract.rep_abs_of_pred (C : TypeDefContract) (ρ : TypeVal)
    (hρ : Admissible ρ) {x : Ty.denote ρ C.family.repTy}
    (hx : C.family.pred ρ hρ x) : C.rep ρ hρ (C.abs ρ hρ x) = x :=
  C.family.rep_abs_of_pred ρ hρ hx

end QEDFV.HOL
