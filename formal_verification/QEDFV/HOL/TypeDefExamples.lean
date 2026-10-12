import QEDFV.HOL.ModelExtension

/-! Two worked gates over `bool`: the predicate `λx. True` (nonempty) and `λx. False`
(empty). The first satisfies the three laws; for the second, the law `P (Rep a)` is not valid,
so the witness hypothesis of `valid_repRange` cannot be dropped. -/
namespace QEDFV.HOL

/-- Constant `0` is `Rep` and constant `1` is `Abs` of the nullary constructor `0` over `bool`. -/
def exSig : Signature := fun c ↦
  if c = 0 then .arr (paramTy 0 0) .bool else if c = 1 then .arr .bool (paramTy 0 0) else .bool

/-- A gate for constructor `0` (arity `0`) with representation type `bool`. -/
def exGate (p : Term exSig [] (.arr .bool .bool)) (hc : ∀ i, i ∈ p.annotVars → i < 0)
    (hk : 0 ∉ p.tyCons) (hr : 0 ∉ p.constIds) (ha : 1 ∉ p.constIds) : TypeDefGate exSig where
  k := 0
  n := 0
  repTy := .bool
  pred := p
  rep := 0
  abs := 1
  rep_ty := by simp [exSig]
  abs_ty := by simp [exSig]
  closed := hc
  k_fresh := hk
  rep_ne_abs := by decide
  rep_fresh := hr
  abs_fresh := ha

/-- The predicate `λx. True`. -/
def trueGate : TypeDefGate exSig :=
  exGate (Term.lam Term.truth) (fun i hi ↦ by simp [Term.annotVars, Ty.typeVars] at hi)
    (by simp [Term.tyCons, Ty.tyCons]) (by simp [Term.constIds]) (by simp [Term.constIds])

/-- The predicate `λx. False`. -/
def falseGate : TypeDefGate exSig :=
  exGate (Term.lam Term.falsity) (fun i hi ↦ by simp [Term.annotVars, Ty.typeVars] at hi)
    (by simp [Term.tyCons, Ty.tyCons]) (by simp [Term.constIds]) (by simp [Term.constIds])

/-- The starting model of the examples. -/
noncomputable def exModel : Model exSig :=
  { κ := defaultTyCon, adm := defaultTyCon_isAdmissible
  , I := canonicalConstVal defaultTyCon exSig }

theorem trueGate_predLocal : trueGate.PredLocal exModel.I :=
  fun c hc ↦ by simp [trueGate, exGate, Term.constIds] at hc

theorem trueGate_witness : trueGate.WitnessAt exModel.I :=
  fun _ _ ↦ ⟨True, trivial⟩

/-- All three laws hold for the nonempty predicate, in the model after the step. -/
theorem trueGate_laws :
    Valid (trueGate.interpret exModel).I trueGate.absRepSequent ∧
    Valid (trueGate.interpret exModel).I trueGate.repRangeSequent ∧
    Valid (trueGate.interpret exModel).I trueGate.repAbsSequent :=
  ⟨trueGate.valid_absRep exModel.adm exModel.I,
   trueGate.valid_repRange exModel.adm exModel.I trueGate_predLocal trueGate_witness,
   trueGate.valid_repAbs exModel.adm exModel.I trueGate_predLocal⟩

/-- Without a witness the law `P (Rep a)` fails: `WitnessAt` cannot be dropped from
`TypeDefGate.valid_repRange`. -/
theorem falseGate_repRange_not_valid :
    ¬ Valid (falseGate.interpret exModel).I falseGate.repRangeSequent := by
  intro h
  have hρ : Admissible (falseGate.newTyCon exModel.I) baseTypeVal :=
    (falseGate.admissible_new_iff exModel.adm exModel.I _).mp
      ⟨fun _ ↦ ⟨()⟩, exModel.adm⟩
  obtain ⟨x⟩ := (falseGate.newTy.carrier_nonempty _ baseTypeVal hρ)
  have := h baseTypeVal hρ (Env.extend closedEnv x) (fun _ hh ↦ nomatch hh)
  change (falseGate.predIn [falseGate.newTy]).eval (falseGate.newConst exModel.adm exModel.I)
    baseTypeVal hρ (Env.extend closedEnv x)
    (falseGate.repTerm.eval (falseGate.newConst exModel.adm exModel.I) baseTypeVal hρ
      (Env.extend closedEnv x) (Env.extend closedEnv x _ Var.zero)) at this
  rw [TypeDefGate.eval_predIn] at this
  exact this

end QEDFV.HOL
