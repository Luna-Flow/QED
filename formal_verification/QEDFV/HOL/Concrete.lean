import QEDFV.HOL.Derivation

namespace QEDFV.HOL

/-! A small concrete signature used for the non-triviality witness. The first
two constants are zero and successor; all remaining constants are interpreted
by the canonical inhabited carrier choice. -/
def standardSignature : Signature
  | 0 => .ind
  | 1 => .arr .ind .ind
  | _ => .bool

noncomputable def standardConstVal : ConstVal standardSignature := fun ρ hρ c ↦
  match c with
  | 0 => (0 : Nat)
  | 1 => (Nat.succ : Nat → Nat)
  | n + 2 => Classical.choice ((standardSignature (n + 2)).carrier_nonempty ρ hρ)

def emptyEnv : Env baseTypeVal [] := fun _ v ↦ by cases v

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

theorem signatureGenericFalseSentence_not_valid (S : Signature) (I : ConstVal S) :
    ¬ Valid I { hyps := [], concl := signatureGenericFalseSentence S } := by
  intro hValid
  have h := hValid baseTypeVal baseTypeVal_admissible emptyEnv (by
    intro h hh
    cases hh)
  change (fun x : Prop => x) = (fun x : Prop => x = x) at h
  have hFalse := congrFun h False
  exact hFalse.symm ▸ (show False = False from rfl)

theorem signatureGenericFalseSentence_not_derivable (S : Signature)
    (hChoice : ChoiceNatural) :
    ¬ Derivation S { hyps := [], concl := signatureGenericFalseSentence S } := by
  intro d
  exact signatureGenericFalseSentence_not_valid S (canonicalConstVal S)
    (derivation_sound hChoice (canonicalConstVal S) d)

end QEDFV.HOL
