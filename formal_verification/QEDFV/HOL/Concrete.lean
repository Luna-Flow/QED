import QEDFV.HOL.Derivation

namespace QEDFV.HOL

variable {κ : TyConVal}

/-! A small concrete signature used for the non-triviality witness. The first
two constants are zero and successor; all remaining constants are interpreted
by the canonical inhabited carrier choice. -/
def standardSignature : Signature
  | 0 => .ind
  | 1 => .arr .ind .ind
  | _ => .bool

noncomputable def standardConstVal : ConstVal defaultTyCon standardSignature := fun ρ hρ c ↦
  match c with
  | 0 => (0 : Nat)
  | 1 => (Nat.succ : Nat → Nat)
  | n + 2 => Classical.choice ((standardSignature (n + 2)).carrier_nonempty defaultTyCon ρ hρ)

def emptyEnv : Env κ baseTypeVal [] := fun _ v ↦ by cases v

def zeroTerm : Term standardSignature [] .ind := .const 0 Ty.var

def succTerm : Term standardSignature [] (.arr .ind .ind) := .const 1 Ty.var

def falseSentence : Term standardSignature [] .bool :=
  (succTerm.app zeroTerm).equal zeroTerm

theorem falseSentence_eval :
    falseSentence.eval standardConstVal baseTypeVal baseTypeVal_admissible emptyEnv = False := by
  simp only [falseSentence, zeroTerm, succTerm, Term.eval, standardConstVal]
  exact propext (by simp)

theorem falseSentence_not_valid :
    ¬ Valid standardConstVal { hyps := [], concl := falseSentence } := by
  intro hValid
  have h := hValid baseTypeVal baseTypeVal_admissible emptyEnv (by
    intro h hh
    cases hh)
  rw [falseSentence_eval] at h
  exact h

theorem falseSentence_not_derivable
    (hChoice : ChoiceNatural) :
    ¬ Derivation standardSignature { hyps := [], concl := falseSentence } := by
  intro d
  exact falseSentence_not_valid (derivation_sound hChoice standardConstVal d)

theorem standard_ind_infinity_anchor :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ :=
  ind_infinity_anchor

def signatureGenericFalseSentence (S : Signature) : Term S [] .bool :=
  (Term.lam (Term.var Var.zero)).equal
    (Term.lam ((Term.var Var.zero).equal (Term.var Var.zero)))

theorem signatureGenericFalseSentence_not_valid (S : Signature) (I : ConstVal κ S)
    (hκ : Admissible κ baseTypeVal) :
    ¬ Valid I { hyps := [], concl := signatureGenericFalseSentence S } := by
  intro hValid
  have h := hValid baseTypeVal hκ emptyEnv (by
    intro h hh
    cases hh)
  change (fun x : Prop => x) = (fun x : Prop => x = x) at h
  have hFalse := congrFun h False
  exact hFalse.symm ▸ (show False = False from rfl)

theorem signatureGenericFalseSentence_not_derivable (S : Signature)
    (hChoice : ChoiceNatural) :
    ¬ Derivation S { hyps := [], concl := signatureGenericFalseSentence S } := by
  intro d
  exact signatureGenericFalseSentence_not_valid S (canonicalConstVal defaultTyCon S)
    baseTypeVal_admissible (derivation_sound hChoice (canonicalConstVal defaultTyCon S) d)

/-! Type-constructor nodes under the default (`PUnit`) constructor interpretation. -/

/-- A constructor node of arity two denotes the interpreted carrier. -/
example : Ty.denote defaultTyCon baseTypeVal (.con 7 2 fun j ↦ if j.val = 0 then .bool else .ind) =
    PUnit := rfl

/-- Constructor types are inhabited under every admissible interpretation. -/
example : Nonempty (Ty.denote defaultTyCon baseTypeVal (.con 7 1 fun _ ↦ .ind)) :=
  Ty.carrier_nonempty _ defaultTyCon baseTypeVal baseTypeVal_admissible

/-- A signature with one constant of a constructor type, and its constant interpretation. -/
def conSignature : Signature := fun _ ↦ .con 3 1 fun _ ↦ .bool

noncomputable def conConstVal : ConstVal defaultTyCon conSignature := fun ρ hρ c ↦
  Classical.choice ((conSignature c).carrier_nonempty defaultTyCon ρ hρ)

example : Term conSignature [] (.con 3 1 fun _ ↦ .bool) := .const 0 Ty.var

/-- A term of constructor type evaluates, and the reflexivity theorem over it is valid. -/
example : (Term.const (S := conSignature) 0 Ty.var).eval conConstVal baseTypeVal
    baseTypeVal_admissible emptyEnv = PUnit.unit := rfl

example : Valid conConstVal (Γ := [])
    { hyps := [], concl := (Term.const (S := conSignature) (Γ := []) 0 Ty.var).equal
        (.const 0 Ty.var) } :=
  valid_refl conConstVal _

end QEDFV.HOL
