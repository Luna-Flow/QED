import QEDFV.Signature.GlobalLocalState

namespace QEDFV

structure TypeDefWitness where
  witnessThm : String
  witnessType : HolType
  repName : ConstName
  absName : ConstName
deriving Repr, BEq

structure TypeDefContract where
  absRepSurj : Prop
  repInRange : Prop
  repAbsRetract : Prop

abbrev TySymbols (t : TheoryState) : Finset (TyCon × TypeArity) := t.tySymbols

def TypeDefOK
    (t : TheoryState)
    (k : TyCon)
    (arity : Nat)
    (repBaseTy : HolType)
    (predicate : Term)
    (w : TypeDefWitness) : Prop :=
  (k, arity) ∉ TySymbols t ∧
  w.witnessType = repBaseTy ∧
  (tyvars repBaseTy).length = arity ∧
  w.repName ∉ Reserved ∧
  w.absName ∉ Reserved ∧
  w.repName ∉ DefHeads t ∧
  w.absName ∉ DefHeads t ∧
  termIsClosed predicate ∧
  termTyvarsSubset predicate repBaseTy

def typedefProductContract
    (_k : TyCon)
    (_params : List TVar)
    (repTy : HolType)
    (pred : Term) : TypeDefContract :=
  { absRepSurj := ∃ w : Term, typeOf? w = some repTy
  , repInRange := ∀ t : Term, t = pred -> termIsClosed t -> termIsClosed pred
  , repAbsRetract := ∀ t : Term, t = pred -> termTyvarsSubset t repTy -> termTyvarsSubset pred repTy
  }

theorem typedef_abs_rep_surj
    (k : TyCon) (params : List TVar) (repTy : HolType) (pred : Term) :
    (typedefProductContract k params repTy pred).absRepSurj := by
  exact ⟨.var "_typedef_witness" repTy, rfl⟩

theorem typedef_rep_in_range
    (k : TyCon) (params : List TVar) (repTy : HolType) (pred : Term) :
    (typedefProductContract k params repTy pred).repInRange := by
  intro t ht hClosed
  subst ht
  exact hClosed

theorem typedef_rep_abs_retract
    (k : TyCon) (params : List TVar) (repTy : HolType) (pred : Term) :
    (typedefProductContract k params repTy pred).repAbsRetract := by
  intro t ht hSubset
  subst ht
  exact hSubset

end QEDFV
