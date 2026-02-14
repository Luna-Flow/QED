import QEDFV.Foundation.Notation

namespace QEDFV

inductive HolType where
  | tyvar : TVar -> HolType
  | tyapp : TyCon -> List HolType -> HolType
deriving Repr, BEq

abbrev boolTy : HolType := HolType.tyapp "bool" []
abbrev indTy : HolType := HolType.tyapp "ind" []
def funTy (a b : HolType) : HolType := HolType.tyapp "fun" [a, b]

def tyvars : HolType -> List TVar
  | .tyvar v => [v]
  | .tyapp _ args => args.foldr (fun t acc => tyvars t ++ acc) []

def tyvarsSubset (lhs rhs : HolType) : Prop :=
  forall v, v ∈ tyvars lhs -> v ∈ tyvars rhs

theorem tyvarsSubset_refl (ty : HolType) : tyvarsSubset ty ty := by
  intro v hv
  exact hv

end QEDFV
