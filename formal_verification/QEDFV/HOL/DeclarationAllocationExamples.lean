import QEDFV.HOL.DeclarationAllocation
import QEDFV.HOL.TypeDefExamples

/-! Concrete allocation evidence for a type-definition gate. The example records the two
constant declarations introduced by `trueGate` and checks them against the existing total
signature `exSig`. -/
namespace QEDFV.HOL

def trueTable0 : DeclTable := ⟨[], by simp⟩

def trueTable1 : DeclTable :=
  trueTable0.add trueGate.rep (TypeDefGate.repAllocation trueGate).ty (by
    simp [trueTable0, DeclTable.ids, trueGate, exGate])

theorem trueTable1_ids : trueTable1.ids = {0} := by
  ext c
  simp [trueTable1, trueTable0, DeclTable.ids, DeclTable.add, trueGate, exGate]

theorem trueTable2_fresh : trueGate.abs ∉ trueTable1.ids := by
  rw [trueTable1_ids]
  simp [trueGate, exGate]

def trueTable2 : DeclTable :=
  trueTable1.add trueGate.abs (TypeDefGate.absAllocation trueGate).ty trueTable2_fresh

theorem trueTable2_compatible : DeclTable.Compatible exSig trueTable2 := by
  have h0 : DeclTable.Compatible exSig trueTable0 := DeclTable.compatible_empty exSig
  have h1 : DeclTable.Compatible exSig trueTable1 :=
    DeclTable.add_allocation_compatible h0 (TypeDefGate.repAllocation trueGate) (by
      simp [trueTable0, DeclTable.ids, trueGate, exGate])
  have h2 : DeclTable.Compatible exSig
      (trueTable1.add trueGate.abs (TypeDefGate.absAllocation trueGate).ty trueTable2_fresh) :=
    DeclTable.add_allocation_compatible h1 (TypeDefGate.absAllocation trueGate) trueTable2_fresh
  change DeclTable.Compatible exSig
    (trueTable1.add trueGate.abs (TypeDefGate.absAllocation trueGate).ty trueTable2_fresh)
  exact h2

theorem trueTable2_preserves_rep :
    trueTable2.Declares trueGate.rep (TypeDefGate.repAllocation trueGate).ty := by
  have h := DeclTable.old_declares_after_add (T := trueTable1)
    (c := trueGate.abs) (a := (TypeDefGate.absAllocation trueGate).ty) (by
      rw [trueTable1_ids]
      simp [trueGate, exGate])
    (DeclTable.add_declares_new (T := trueTable0)
      (c := trueGate.rep) (a := (TypeDefGate.repAllocation trueGate).ty) (by
        simp [trueTable0, DeclTable.ids, trueGate, exGate]))
  simpa [trueTable2] using h

theorem trueTable2_has_abs :
    trueTable2.Declares trueGate.abs (TypeDefGate.absAllocation trueGate).ty := by
  have h := DeclTable.add_declares_new (T := trueTable1)
    (c := trueGate.abs) (a := (TypeDefGate.absAllocation trueGate).ty) (by
      rw [trueTable1_ids]
      simp [trueGate, exGate])
  simpa [trueTable2] using h

theorem trueTable2_rep_type_is_stable :
    exSig trueGate.rep = (TypeDefGate.repAllocation trueGate).ty :=
  (trueTable2_compatible trueTable2_preserves_rep)

theorem trueTable2_abs_type_is_stable :
    exSig trueGate.abs = (TypeDefGate.absAllocation trueGate).ty :=
  (trueTable2_compatible trueTable2_has_abs)

end QEDFV.HOL
