import QEDFV.Subst.TypeSubst

namespace QEDFV

structure ConstSchemeEnv where
  schemes : List (ConstName × HolType)
deriving Repr

def lookupConstScheme (env : ConstSchemeEnv) (c : ConstName) : Option HolType :=
  match env.schemes.find? (fun p => p.fst = c) with
  | some (_, tyGen) => some tyGen
  | none => none

def TyInstance (ty tyGen : HolType) : Prop :=
  ∃ theta : TypeSubst, applyTypeSubst theta tyGen = ty

def admissibleConstInstance
    (env : ConstSchemeEnv) (c : ConstName) (ty : HolType) : Prop :=
  ∃ tyGen, lookupConstScheme env c = some tyGen ∧ TyInstance ty tyGen

theorem tyInstance_refl (ty : HolType) : TyInstance ty ty := by
  exact ⟨[], applyTypeSubst_nil ty⟩

theorem const_instance_from_principal
    (env : ConstSchemeEnv) (c : ConstName) (tyGen ty : HolType)
    (hLookup : lookupConstScheme env c = some tyGen)
    (hInst : TyInstance ty tyGen) :
    admissibleConstInstance env c ty := by
  exact ⟨tyGen, hLookup, hInst⟩

theorem no_monomorphic_lockout
    (env : ConstSchemeEnv)
    (c : ConstName)
    (tyGen ty1 ty2 : HolType)
    (hLookup : lookupConstScheme env c = some tyGen)
    (h1 : TyInstance ty1 tyGen)
    (h2 : TyInstance ty2 tyGen) :
    admissibleConstInstance env c ty1 ∧ admissibleConstInstance env c ty2 := by
  exact ⟨
    const_instance_from_principal env c tyGen ty1 hLookup h1,
    const_instance_from_principal env c tyGen ty2 hLookup h2
  ⟩

end QEDFV
