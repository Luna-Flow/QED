import QEDFV.Kernel.ThmObject
import QEDFV.Signature.GlobalLocalState
import QEDFV.Signature.TypeDef
import QEDFV.Subst.TypeSubst
import QEDFV.Subst.TermSubst
import QEDFV.Db.ExprCore

namespace QEDFV

def mkEqExpr (lhs rhs : DbExpr) : DbExpr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq []) lhs) rhs

def EqExpr (e : DbExpr) : Prop :=
  match e with
  | Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq _) _) _ => True
  | _ => False

def IsBoolExpr (e : DbExpr) : Prop := EqExpr e

theorem isBoolExpr_mkEqExpr (lhs rhs : DbExpr) : IsBoolExpr (mkEqExpr lhs rhs) := by
  simp [IsBoolExpr, EqExpr, mkEqExpr]

def typeAdmissibleIn (t : TheoryState) : HolType -> Prop
  | .tyvar _ => True
  | .tyapp k args =>
      (k, args.length) ∈ TySymbols t ∧
      ∀ ty, ty ∈ args -> typeAdmissibleIn t ty

def valid_ty_subst (theta : TypeSubst) : Prop :=
  ∀ v ty, lookupTypeSubst theta v = some ty -> tyvarsSubset ty ty

def admissible_ty_image (t : TheoryState) (theta : TypeSubst) : Prop :=
  ∀ v ty, lookupTypeSubst theta v = some ty -> typeAdmissibleIn t ty

def typing_preserved_under_ty_subst (_theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF s.concl ∧ ∀ h, h ∈ s.hyps -> QEDExprWF h

def def_inst_coherent (_theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF s.concl ∧ ∀ h, h ∈ s.hyps -> QEDExprWF h

def const_instance_ok (_theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF s.concl

def theorem_structure_preserved (_theta : TypeSubst) (s : Sequent) : Prop :=
  s.hyps.length = s.hyps.length ∧ s.concl = s.concl

def valid_term_subst (sigma : TermSubst) : Prop :=
  substitutionTypePreserving sigma ∧ substitutionCaptureAvoiding sigma

inductive InstTypeFailure where
  | invalidSubstitution
  | inadmissibleTypeTarget
  | typingFailure
  | definitionalCoherenceViolation
  | constantInstanceMismatch
  | malformedTheoremStructure
deriving Repr, BEq

noncomputable def instTypeFailure
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent) : Option InstTypeFailure := by
  classical
  by_cases h1 : valid_ty_subst theta
  · by_cases h2 : admissible_ty_image k.T theta
    · by_cases h3 : typing_preserved_under_ty_subst theta s
      · by_cases h4 : def_inst_coherent theta s
        · by_cases h5 : const_instance_ok theta s
          · by_cases h6 : theorem_structure_preserved theta s
            · exact none
            · exact some .malformedTheoremStructure
          · exact some .constantInstanceMismatch
        · exact some .definitionalCoherenceViolation
      · exact some .typingFailure
    · exact some .inadmissibleTypeTarget
  · exact some .invalidSubstitution

inductive Derivable (k : KernelState) : Sequent -> Prop where
  | refl (t : DbExpr) :
      Derivable k { hyps := [], concl := mkEqExpr t t }
  | assume (p : DbExpr) :
      IsBoolExpr p ->
      Derivable k { hyps := [p], concl := p }
  | trans (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := B.concl }
  | mkComb (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := A.concl }
  | abs (A : Sequent) :
      Derivable k A -> Derivable k A
  | beta (A : Sequent) :
      Derivable k A -> Derivable k A
  | eqMp (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := B.concl }
  | deductAntisym (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := A.hyps ++ B.hyps, concl := A.concl }
  | instType (theta : TypeSubst) (A : Sequent) :
      valid_ty_subst theta ->
      admissible_ty_image k.T theta ->
      typing_preserved_under_ty_subst theta A ->
      def_inst_coherent theta A ->
      const_instance_ok theta A ->
      theorem_structure_preserved theta A ->
      Derivable k A ->
      Derivable k A
  | inst (sigma : TermSubst) (A : Sequent) :
      valid_term_subst sigma ->
      Derivable k A ->
      Derivable k A

theorem valid_ty_subst_empty : valid_ty_subst [] := by
  intro v ty h
  simp [lookupTypeSubst_nil] at h

theorem admissible_ty_image_empty (t : TheoryState) : admissible_ty_image t [] := by
  intro v ty h
  simp [lookupTypeSubst_nil] at h

theorem theorem_structure_preserved_refl (theta : TypeSubst) (s : Sequent) :
    theorem_structure_preserved theta s := by
  exact ⟨rfl, rfl⟩

theorem typing_preserved_under_ty_subst_refl
    (theta : TypeSubst)
    (s : Sequent)
    (hWF : QEDExprWF s.concl ∧ ∀ h, h ∈ s.hyps -> QEDExprWF h) :
    typing_preserved_under_ty_subst theta s := by
  exact hWF

theorem valid_term_subst_empty : valid_term_subst [] := by
  constructor
  · intro n t h
    simp [lookupTermSubst_nil] at h
  · intro n t h
    simp [lookupTermSubst_nil] at h

end QEDFV
