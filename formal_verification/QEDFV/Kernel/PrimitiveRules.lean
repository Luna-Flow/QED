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

def holTypeToLevel : HolType -> Lean.Level
  | .tyvar v => .param (.str .anonymous v)
  | .tyapp k args =>
      args.foldl (fun acc ty => .max acc (holTypeToLevel ty)) (.param (.str .anonymous k))

def thetaLevels (theta : TypeSubst) : List Lean.Level :=
  theta.map (fun p => holTypeToLevel p.snd)

partial def applyTypeSubstExpr (theta : TypeSubst) : DbExpr -> DbExpr
  | .app f a => .app (applyTypeSubstExpr theta f) (applyTypeSubstExpr theta a)
  | .lam n ty body bi =>
      .lam n (applyTypeSubstExpr theta ty) (applyTypeSubstExpr theta body) bi
  | .forallE n ty body bi =>
      .forallE n (applyTypeSubstExpr theta ty) (applyTypeSubstExpr theta body) bi
  | .letE n ty val body nonDep =>
      .letE n (applyTypeSubstExpr theta ty) (applyTypeSubstExpr theta val)
        (applyTypeSubstExpr theta body) nonDep
  | .mdata md body => .mdata md (applyTypeSubstExpr theta body)
  | .proj n i body => .proj n i (applyTypeSubstExpr theta body)
  | .const n ls => .const n (ls ++ thetaLevels theta)
  | e => e

def applyTypeSubstSequent (theta : TypeSubst) (s : Sequent) : Sequent :=
  { hyps := s.hyps.map (applyTypeSubstExpr theta)
  , concl := applyTypeSubstExpr theta s.concl
  }

def typing_preserved_under_ty_subst (theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF (applyTypeSubstExpr theta s.concl) ∧
    ∀ h, h ∈ (applyTypeSubstSequent theta s).hyps -> QEDExprWF h

def def_inst_coherent (_theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF s.concl ∧ ∀ h, h ∈ s.hyps -> QEDExprWF h

def const_instance_ok (_theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF s.concl

def theorem_structure_preserved (theta : TypeSubst) (s : Sequent) : Prop :=
  (applyTypeSubstSequent theta s).hyps.length = s.hyps.length

def valid_term_subst (sigma : TermSubst) : Prop :=
  substitutionTypePreserving sigma ∧ substitutionCaptureAvoiding sigma

partial def termToDbExprApprox : Term -> DbExpr
  | .var _ _ => .bvar 0
  | .const n _ => .const (.str .anonymous n) []
  | .comb f x => .app (termToDbExprApprox f) (termToDbExprApprox x)
  | .abs n _ body => .lam (.str .anonymous n) (.const `Unit []) (termToDbExprApprox body) .default

partial def applyTermSubstExpr (_sigma : TermSubst) : DbExpr -> DbExpr
  | .bvar i =>
      match _sigma.drop i with
      | (_, t) :: _ => termToDbExprApprox t
      | [] => .bvar i
  | .app f a => .app (applyTermSubstExpr _sigma f) (applyTermSubstExpr _sigma a)
  | .lam n ty body bi =>
      .lam n (applyTermSubstExpr _sigma ty) (applyTermSubstExpr _sigma body) bi
  | .forallE n ty body bi =>
      .forallE n (applyTermSubstExpr _sigma ty) (applyTermSubstExpr _sigma body) bi
  | .letE n ty val body nonDep =>
      .letE n (applyTermSubstExpr _sigma ty) (applyTermSubstExpr _sigma val)
        (applyTermSubstExpr _sigma body) nonDep
  | .mdata md body => .mdata md (applyTermSubstExpr _sigma body)
  | .proj n i body => .proj n i (applyTermSubstExpr _sigma body)
  | e => e

def applyTermSubstSequent (sigma : TermSubst) (s : Sequent) : Sequent :=
  { hyps := s.hyps.map (applyTermSubstExpr sigma)
  , concl := applyTermSubstExpr sigma s.concl
  }

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
      Derivable k { hyps := hypsUnion A.hyps B.hyps, concl := B.concl }
  | mkComb (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := hypsUnion A.hyps B.hyps, concl := A.concl }
  | abs (A : Sequent) :
      Derivable k A -> Derivable k A
  | beta (A : Sequent) :
      Derivable k A -> Derivable k A
  | eqMp (A B : Sequent) :
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := hypsUnion A.hyps B.hyps, concl := B.concl }
  | deductAntisym (A B : Sequent) :
      alphaSetEq
        (hypsUnion (hypsRemove A.hyps B.concl) (hypsRemove B.hyps A.concl))
        (hypsUnion A.hyps B.hyps) ->
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := hypsUnion A.hyps B.hyps, concl := mkEqExpr A.concl B.concl }
  | instType (theta : TypeSubst) (A : Sequent) :
      valid_ty_subst theta ->
      admissible_ty_image k.T theta ->
      typing_preserved_under_ty_subst theta A ->
      def_inst_coherent theta A ->
      const_instance_ok theta A ->
      theorem_structure_preserved theta A ->
      Derivable k A ->
      Derivable k (applyTypeSubstSequent theta A)
  | inst (sigma : TermSubst) (A : Sequent) :
      valid_term_subst sigma ->
      Derivable k A ->
      Derivable k (applyTermSubstSequent sigma A)

theorem valid_ty_subst_empty : valid_ty_subst [] := by
  intro v ty h
  simp [lookupTypeSubst_nil] at h

theorem admissible_ty_image_empty (t : TheoryState) : admissible_ty_image t [] := by
  intro v ty h
  simp [lookupTypeSubst_nil] at h

theorem theorem_structure_preserved_refl (theta : TypeSubst) (s : Sequent) :
    theorem_structure_preserved theta s := by
  simp [theorem_structure_preserved, applyTypeSubstSequent]

theorem typing_preserved_under_ty_subst_refl
    (theta : TypeSubst)
    (s : Sequent)
    (hWF : QEDExprWF (applyTypeSubstExpr theta s.concl) ∧
      ∀ h, h ∈ (applyTypeSubstSequent theta s).hyps -> QEDExprWF h) :
    typing_preserved_under_ty_subst theta s := by
  exact hWF

theorem valid_term_subst_empty : valid_term_subst [] := by
  constructor
  · intro n t h
    simp [lookupTermSubst_nil] at h
  · intro n t h
    simp [lookupTermSubst_nil] at h

end QEDFV
