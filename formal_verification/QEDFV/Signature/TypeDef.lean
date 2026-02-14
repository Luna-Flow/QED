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
  , repInRange := termIsClosed pred -> termIsClosed pred
  , repAbsRetract := termTyvarsSubset pred repTy -> termTyvarsSubset pred repTy
  }

end QEDFV
