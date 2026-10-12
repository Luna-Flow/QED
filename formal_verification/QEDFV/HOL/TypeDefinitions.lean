import QEDFV.HOL.Extensions

namespace QEDFV.HOL

variable {κ : TyConVal}

/-! Parametric semantic content of a type-definition gate. The predicate and its
witness are quantified over every admissible interpretation of the declared
type variables. -/
structure PredicateFamily (κ : TyConVal) where
  repTy : Ty
  pred : (ρ : TypeVal) → Admissible κ ρ → Ty.denote κ ρ repTy → Prop
  witness : ∀ (ρ : TypeVal) (hρ : Admissible κ ρ), ∃ x, pred ρ hρ x

def PredicateFamily.witnessAt (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) : PredicateWitness (Ty.denote κ ρ F.repTy) (F.pred ρ hρ) :=
  ⟨F.witness ρ hρ⟩

noncomputable def PredicateFamily.abs (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (x : Ty.denote κ ρ F.repTy) :
    {y : Ty.denote κ ρ F.repTy // F.pred ρ hρ y} :=
  (F.witnessAt ρ hρ).abs x

def PredicateFamily.rep (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ F.repTy // F.pred ρ hρ y}) : Ty.denote κ ρ F.repTy :=
  (F.witnessAt ρ hρ).rep x

theorem PredicateFamily.carrier_nonempty (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) :
    Nonempty {y : Ty.denote κ ρ F.repTy // F.pred ρ hρ y} :=
  (F.witnessAt ρ hρ).carrier_nonempty

theorem PredicateFamily.abs_rep (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ F.repTy // F.pred ρ hρ y}) :
    F.abs ρ hρ (F.rep ρ hρ x) = x := by
  exact (F.witnessAt ρ hρ).abs_rep x

theorem PredicateFamily.rep_in_range (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ F.repTy // F.pred ρ hρ y}) :
    F.pred ρ hρ (F.rep ρ hρ x) :=
  x.property

theorem PredicateFamily.rep_abs_of_pred (F : PredicateFamily κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) {x : Ty.denote κ ρ F.repTy} (hx : F.pred ρ hρ x) :
    F.rep ρ hρ (F.abs ρ hρ x) = x := by
  exact (F.witnessAt ρ hρ).rep_abs_of_pred hx

structure TypeDefContract (κ : TyConVal) where
  family : PredicateFamily κ

noncomputable def TypeDefContract.abs (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) (x : Ty.denote κ ρ C.family.repTy) :
    {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.family.abs ρ hρ x

def TypeDefContract.rep (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}) :
    Ty.denote κ ρ C.family.repTy :=
  C.family.rep ρ hρ x

theorem TypeDefContract.nonempty (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) :
    Nonempty {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y} :=
  C.family.carrier_nonempty ρ hρ

theorem TypeDefContract.abs_rep (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}) :
    C.abs ρ hρ (C.rep ρ hρ x) = x :=
  C.family.abs_rep ρ hρ x

theorem TypeDefContract.rep_in_range (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ)
    (x : {y : Ty.denote κ ρ C.family.repTy // C.family.pred ρ hρ y}) :
    C.family.pred ρ hρ (C.rep ρ hρ x) :=
  C.family.rep_in_range ρ hρ x

theorem TypeDefContract.rep_abs_of_pred (C : TypeDefContract κ) (ρ : TypeVal)
    (hρ : Admissible κ ρ) {x : Ty.denote κ ρ C.family.repTy}
    (hx : C.family.pred ρ hρ x) : C.rep ρ hρ (C.abs ρ hρ x) = x :=
  C.family.rep_abs_of_pred ρ hρ hx

end QEDFV.HOL
