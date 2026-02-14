import QEDFV.Signature.TypeDef
import QEDFV.Extension.DefOK

namespace QEDFV

structure SpecIntro where
  c : ConstName
  ty : HolType
  predicate : Term
  witness : Thm
deriving Repr

def emptyHyps (th : Thm) : Prop :=
  th.seq.hyps = []

def witnessShape (s : SpecIntro) : Prop :=
  emptyHyps s.witness

def termClosure (s : SpecIntro) : Prop :=
  termIsClosed s.predicate

def typeVarClosure (s : SpecIntro) : Prop :=
  forall v, v ∈ termTyVars s.predicate -> v ∈ tyvars s.ty

def schemaLock (s : SpecIntro) : Prop :=
  s.witness.seq.concl = Lean.Expr.const (Lean.Name.str .anonymous s.c) []

def noImplicitWidening (s : SpecIntro) : Prop :=
  typeVarClosure s

def SpecOK (t : TheoryState) (s : SpecIntro) : Prop :=
  s.c ∉ DefHeads t ∧
  s.c ∉ Reserved ∧
  witnessShape s ∧
  termClosure s ∧
  typeVarClosure s ∧
  schemaLock s ∧
  noImplicitWidening s

def spec_derived_path_obligation (t : TheoryState) (s : SpecIntro) : Prop :=
  SpecOK t s ->
  typeOf? s.predicate = some s.ty ->
  acyclic s.predicate s.c ->
  ∃ d : DefIntro,
    d.c = s.c ∧
    d.ty = s.ty ∧
    d.rhs = s.predicate ∧
    DefOK t d

def spec_extension_conservative (t : TheoryState) (s : SpecIntro) : Prop :=
  SpecOK t s -> forall c, c ∈ DefHeads t -> c ≠ s.c

theorem spec_derived_path_obligation_proved (t : TheoryState) (s : SpecIntro) :
    spec_derived_path_obligation t s := by
  intro hSpec hTy hAcyclic
  refine ⟨{ c := s.c, ty := s.ty, rhs := s.predicate }, rfl, rfl, rfl, ?_⟩
  rcases hSpec with ⟨hFresh, hReserved, _, hClosed, hTyVar, _, _⟩
  exact ⟨hFresh, hReserved, hTy, hClosed, hAcyclic, hTyVar⟩

theorem spec_extension_conservative_proved (t : TheoryState) (s : SpecIntro) :
    spec_extension_conservative t s := by
  intro hSpec c hIn
  rcases hSpec with ⟨hFresh, _, _, _, _, _, _⟩
  intro hEq
  subst hEq
  exact hFresh hIn

end QEDFV
