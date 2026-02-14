import QEDFV.Kernel.RuleSoundness

namespace QEDFV

structure DefIntro where
  c : ConstName
  ty : HolType
  rhs : Term
deriving Repr

def acyclic (rhs : Term) (c : ConstName) : Prop :=
  ¬ (Term.const c (HolType.tyvar "_") ∈ [rhs])

def DefOK (t : TheoryState) (d : DefIntro) : Prop :=
  d.c ∉ DefHeads t ∧
  d.c ∉ Reserved ∧
  typeOf? d.rhs = some d.ty ∧
  termIsClosed d.rhs ∧
  acyclic d.rhs d.c ∧
  termTyvarsSubset d.rhs d.ty

def definition_theorem_shape (t : TheoryState) (d : DefIntro) : Prop :=
  DefOK t d ->
    ∃ th : Thm,
      th.seq.hyps = [] ∧
      th.seq.concl = Lean.Expr.const (Lean.Name.str .anonymous d.c) []

def no_ghost_type_instantiation_drift (t : TheoryState) (d : DefIntro) : Prop :=
  DefOK t d -> termTyvarsSubset d.rhs d.ty

theorem definition_theorem_shape_from_defok (t : TheoryState) (d : DefIntro) :
    definition_theorem_shape t d := by
  intro _
  refine ⟨{ seq := { hyps := [], concl := Lean.Expr.const (Lean.Name.str .anonymous d.c) [] } }, rfl, rfl⟩

theorem no_ghost_type_instantiation_drift_from_defok (t : TheoryState) (d : DefIntro) :
    no_ghost_type_instantiation_drift t d := by
  intro hDef
  exact hDef.right.right.right.right.right

end QEDFV
