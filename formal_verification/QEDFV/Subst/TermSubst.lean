import QEDFV.Subst.TypeSubst
import QEDFV.Term.Grammar

namespace QEDFV

abbrev TermSubst := List (String × Term)

def lookupTermSubst (s : TermSubst) (n : String) : Option Term :=
  match s.find? (fun p => p.fst = n) with
  | some (_, t) => some t
  | none => none

def substTerm (s : TermSubst) : Term -> Term
  | .var n ty =>
      match lookupTermSubst s n with
      | some t => t
      | none => .var n ty
  | .const n ty => .const n ty
  | .comb f x => .comb (substTerm s f) (substTerm s x)
  | .abs n ty body =>
      let s' := s.filter (fun p => p.fst != n)
      .abs n ty (substTerm s' body)

def substitutionTypePreserving (s : TermSubst) : Prop :=
  forall n t, lookupTermSubst s n = some t -> exists ty, typeOf? t = some ty

def substitutionCaptureAvoiding (s : TermSubst) : Prop :=
  forall n t, lookupTermSubst s n = some t -> termIsClosed t

@[simp] theorem lookupTermSubst_nil (n : String) :
    lookupTermSubst [] n = none := by
  rfl

@[simp] theorem substTerm_nil : ∀ t : Term, substTerm [] t = t
  | .var n ty => by
      simp [substTerm]
  | .const n ty => by
      simp [substTerm]
  | .comb f x => by
      simp [substTerm, substTerm_nil f, substTerm_nil x]
  | .abs n ty body => by
      simp [substTerm, substTerm_nil body]

@[simp] theorem substTerm_nil_var (n : String) (ty : HolType) :
    substTerm [] (.var n ty) = .var n ty := by
  simp

end QEDFV
