import QEDFV.HOL.ModelExtension

/-! A finite declaration-table interface for the fixed-signature semantics.

The Typed HOL development uses a total `Signature := Nat → Ty`; it does not model an
evolving signature map. `DeclTable` records the finite allocation information needed at the
refinement boundary. Compatibility says that every allocated identifier has the type supplied
by the total signature. The lemmas below prove the part of a growing-signature argument that is
independent of representation: a fresh allocation preserves all old declarations and remains
compatible with the same total signature when its declared type agrees with the signature.

This is deliberately an interface layer, not a replacement for `Signature`, `ModelExtension`,
or the executable kernel state. It leaves name resolution, constructor allocation, and source
level state refinement as separate obligations. -/
namespace QEDFV.HOL

/-- A finite table of allocated constant identifiers and their declared types. -/
structure DeclTable where
  entries : List (Nat × Ty)
  nodup_ids : (entries.map Prod.fst).Nodup

namespace DeclTable

/-- The identifiers allocated by a finite table. -/
def ids (T : DeclTable) : Set Nat := {c | c ∈ T.entries.map Prod.fst}

/-- A table entry is a declaration of identifier `c` with type `a`. -/
def Declares (T : DeclTable) (c : Nat) (a : Ty) : Prop := (c, a) ∈ T.entries

/-- The total fixed signature agrees with every declaration in the table. -/
def Compatible (S : Signature) (T : DeclTable) : Prop :=
  ∀ {c : Nat} {a : Ty}, T.Declares c a → S c = a

theorem fresh_iff_not_mem_map {T : DeclTable} {c : Nat} :
    c ∉ T.ids ↔ c ∉ T.entries.map Prod.fst := Iff.rfl

/-- Add one fresh allocation to a table. The freshness premise is part of the constructor. -/
def add (T : DeclTable) (c : Nat) (a : Ty) (hFresh : c ∉ T.ids) : DeclTable :=
  { entries := (c, a) :: T.entries
  , nodup_ids := by
      apply List.Nodup.cons
      · simpa [ids] using hFresh
      · exact T.nodup_ids }

theorem old_declares_after_add {T : DeclTable} {c c' : Nat} {a a' : Ty}
    (hFresh : c ∉ T.ids) (hOld : T.Declares c' a') :
    (T.add c a hFresh).Declares c' a' := by
  exact List.mem_cons_of_mem _ hOld

theorem old_ids_subset_after_add {T : DeclTable} {c : Nat} {a : Ty}
    (hFresh : c ∉ T.ids) : T.ids ⊆ (T.add c a hFresh).ids := by
  intro c' hc'
  rcases (List.mem_map.mp hc') with ⟨entry, hEntry, hId⟩
  refine List.mem_map.mpr ⟨entry, ?_, hId⟩
  exact List.mem_cons_of_mem _ hEntry

theorem add_id_mem {T : DeclTable} {c : Nat} {a : Ty} (hFresh : c ∉ T.ids) :
    c ∈ (T.add c a hFresh).ids := by
  simp [add, ids]

theorem add_declares_new {T : DeclTable} {c : Nat} {a : Ty} (hFresh : c ∉ T.ids) :
    (T.add c a hFresh).Declares c a := by
  simp [add, Declares]

theorem compatible_add {S : Signature} {T : DeclTable} {c : Nat} {a : Ty}
    (hCompatible : Compatible S T) (hFresh : c ∉ T.ids) (hType : S c = a) :
    Compatible S (T.add c a hFresh) := by
  intro c' a' hDeclared
  change (c', a') ∈ (c, a) :: T.entries at hDeclared
  rcases List.mem_cons.mp hDeclared with hNew | hOld
  · cases hNew
    exact hType
  · exact hCompatible hOld

theorem declared_type_unique {S : Signature} {T : DeclTable} (hCompatible : Compatible S T)
    {c : Nat} {a a' : Ty} (h₁ : T.Declares c a) (h₂ : T.Declares c a') : a = a' := by
  exact (hCompatible h₁).symm.trans (hCompatible h₂)

theorem compatible_empty (S : Signature) : Compatible S ⟨[], by simp⟩ := by
  intro c a h
  cases h

theorem compatible_add_preserves_old {S : Signature} {T : DeclTable} {c : Nat} {a : Ty}
    (hCompatible : Compatible S T) (hFresh : c ∉ T.ids) (hType : S c = a)
    {c' : Nat} {a' : Ty} (hOld : T.Declares c' a') :
    S c' = a' := by
  exact (compatible_add hCompatible hFresh hType)
    (old_declares_after_add hFresh hOld)

end DeclTable

/-! Gate-facing allocation records. These expose the type slots already present in the total
signature and make the fixed-signature/growing-signature boundary explicit. -/

structure ConstantAllocation (S : Signature) where
  id : Nat
  ty : Ty
  type_eq : S id = ty

def DefinitionGate.allocation {S : Signature} (D : DefinitionGate S) : ConstantAllocation S :=
  { id := D.id, ty := S D.id, type_eq := rfl }

def SpecificationGate.allocation {S : Signature} (G : SpecificationGate S)
    (hTy : S G.id = G.ty) : ConstantAllocation S :=
  { id := G.id, ty := G.ty, type_eq := hTy }

def TypeDefGate.repAllocation {S : Signature} (G : TypeDefGate S) : ConstantAllocation S :=
  { id := G.rep, ty := .arr (paramTy G.k G.n) G.repTy, type_eq := G.rep_ty }

def TypeDefGate.absAllocation {S : Signature} (G : TypeDefGate S) : ConstantAllocation S :=
  { id := G.abs, ty := .arr G.repTy (paramTy G.k G.n), type_eq := G.abs_ty }

theorem allocation_type {S : Signature} (A : ConstantAllocation S) : S A.id = A.ty :=
  A.type_eq

theorem DeclTable.add_allocation_compatible {S : Signature} {T : DeclTable}
    (hCompatible : DeclTable.Compatible S T) (A : ConstantAllocation S)
    (hFresh : A.id ∉ T.ids) : DeclTable.Compatible S (T.add A.id A.ty hFresh) :=
  DeclTable.compatible_add hCompatible hFresh A.type_eq

end QEDFV.HOL
