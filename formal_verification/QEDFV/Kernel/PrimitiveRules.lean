import QEDFV.Kernel.ThmObject
import QEDFV.Signature.GlobalLocalState
import QEDFV.Signature.TypeDef
import QEDFV.Subst.TypeSubst
import QEDFV.Subst.TermSubst
import QEDFV.Db.ExprCore
import QEDFV.Db.Operations
import QEDFV.Db.TypedBeta

namespace QEDFV

def mkEqExpr (lhs rhs : DbExpr) : DbExpr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq []) lhs) rhs

def EqExpr (e : DbExpr) : Prop :=
  match e with
  | Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq _) _) _ => True
  | _ => False

def eqSides? : DbExpr -> Option (DbExpr × DbExpr)
  | Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Eq _) lhs) rhs => some (lhs, rhs)
  | _ => none

def IsBoolExpr (e : DbExpr) : Prop := EqExpr e

theorem isBoolExpr_mkEqExpr (lhs rhs : DbExpr) : IsBoolExpr (mkEqExpr lhs rhs) := by
  simp [IsBoolExpr, EqExpr, mkEqExpr]

theorem eqSides?_mkEqExpr (lhs rhs : DbExpr) :
    eqSides? (mkEqExpr lhs rhs) = some (lhs, rhs) := by
  simp [eqSides?, mkEqExpr]

theorem alphaEq_mkEqExpr_left
    {a b c : DbExpr}
    (h : AlphaEqExpr a b) :
    AlphaEqExpr (mkEqExpr a c) (mkEqExpr b c) := by
  unfold AlphaEqExpr at h ⊢
  simpa [mkEqExpr, alphaNorm] using h

theorem alphaEq_mkEqExpr_right
    {a b c : DbExpr}
    (h : AlphaEqExpr b c) :
    AlphaEqExpr (mkEqExpr a b) (mkEqExpr a c) := by
  unfold AlphaEqExpr at h ⊢
  simpa [mkEqExpr, alphaNorm] using h

def mkCombEqExpr (f g x y : DbExpr) : DbExpr :=
  mkEqExpr (Lean.Expr.app f x) (Lean.Expr.app g y)

def mkAbsEqExpr (n : Lean.Name) (ty s t : DbExpr) : DbExpr :=
  mkEqExpr (Lean.Expr.lam n ty s .default) (Lean.Expr.lam n ty t .default)

def betaRedexExpr (r : TypedBetaRedex) : DbExpr :=
  Lean.Expr.app (Lean.Expr.lam .anonymous r.binderTy r.body .default) r.arg

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

def thetaParamNames (theta : TypeSubst) : Array Lean.Name :=
  theta.toArray.map (fun p => .str .anonymous p.fst)

def thetaLevels (theta : TypeSubst) : Array Lean.Level :=
  theta.toArray.map (fun p => holTypeToLevel p.snd)

def applyTypeSubstExpr (theta : TypeSubst) (e : DbExpr) : DbExpr :=
  e.instantiateLevelParamsArray (thetaParamNames theta) (thetaLevels theta)

def applyTypeSubstSequent (theta : TypeSubst) (s : Sequent) : Sequent :=
  { hyps := s.hyps.map (applyTypeSubstExpr theta)
  , concl := applyTypeSubstExpr theta s.concl
  }

def typing_preserved_under_ty_subst (theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF (applyTypeSubstExpr theta s.concl) ∧
    ∀ h, h ∈ (applyTypeSubstSequent theta s).hyps -> QEDExprWF h

def def_inst_coherent (theta : TypeSubst) (s : Sequent) : Prop :=
  QEDExprWF (applyTypeSubstExpr theta s.concl) ∧
    (∀ h, h ∈ (applyTypeSubstSequent theta s).hyps -> QEDExprWF h) ∧
    match eqSides? s.concl with
    | some (lhs, rhs) =>
        eqSides? (applyTypeSubstExpr theta s.concl) =
          some (applyTypeSubstExpr theta lhs, applyTypeSubstExpr theta rhs)
    | none => True

partial def constHeadPreservedByTySubst (theta : TypeSubst) : DbExpr -> Prop
  | .const n ls =>
      match applyTypeSubstExpr theta (.const n ls) with
      | .const n' _ => n' = n
      | _ => False
  | .app f x => constHeadPreservedByTySubst theta f ∧ constHeadPreservedByTySubst theta x
  | .lam _ ty body _ =>
      constHeadPreservedByTySubst theta ty ∧ constHeadPreservedByTySubst theta body
  | .forallE _ ty body _ =>
      constHeadPreservedByTySubst theta ty ∧ constHeadPreservedByTySubst theta body
  | .letE _ ty val body _ =>
      constHeadPreservedByTySubst theta ty ∧
      constHeadPreservedByTySubst theta val ∧
      constHeadPreservedByTySubst theta body
  | .mdata _ body => constHeadPreservedByTySubst theta body
  | .proj _ _ body => constHeadPreservedByTySubst theta body
  | _ => True

def const_instance_ok (theta : TypeSubst) (s : Sequent) : Prop :=
  constHeadPreservedByTySubst theta s.concl ∧
    ∀ h, h ∈ s.hyps -> constHeadPreservedByTySubst theta h

def theorem_structure_preserved (theta : TypeSubst) (s : Sequent) : Prop :=
  (applyTypeSubstSequent theta s).hyps.length = s.hyps.length

def valid_term_subst (sigma : TermSubst) : Prop :=
  substitutionTypePreserving sigma ∧ substitutionCaptureAvoiding sigma

mutual

partial def holTypeToDbExpr : HolType -> DbExpr
  | .tyvar v => .const (.str .anonymous ("typevar$" ++ v)) []
  | .tyapp k args =>
      args.foldl
        (fun acc ty => .app acc (holTypeToDbExpr ty))
        (.const (.str .anonymous ("typecon$" ++ k)) [])

partial def termToDbExprApprox : Term -> DbExpr
  | .var n _ => .const (.str .anonymous n) []
  | .const n _ => .const (.str .anonymous n) []
  | .comb f x => .app (termToDbExprApprox f) (termToDbExprApprox x)
  | .abs n ty body => .lam (.str .anonymous n) (holTypeToDbExpr ty) (termToDbExprApprox body) .default

end

def lookupTermDbSubst (snapshot : List (Lean.Name × DbExpr)) (n : Lean.Name) : Option DbExpr :=
  match snapshot.find? (fun p => p.fst = n) with
  | some (_, rhs) => some rhs
  | none => none

def dropTermDbSubstKey (snapshot : List (Lean.Name × DbExpr)) (n : Lean.Name) : List (Lean.Name × DbExpr) :=
  snapshot.filter (fun p => p.fst != n)

def termSubstSnapshot (sigma : TermSubst) : List (Lean.Name × DbExpr) :=
  sigma.map (fun p => (.str .anonymous p.fst, termToDbExprApprox p.snd))

def termSubstArray (sigma : TermSubst) : Array DbExpr :=
  sigma.toArray.map (fun p => termToDbExprApprox p.snd)

partial def applyTermSubstExprWith (snapshot : List (Lean.Name × DbExpr)) : DbExpr -> DbExpr
  | .const n ls =>
      match lookupTermDbSubst snapshot n with
      | some rhs => rhs
      | none => .const n ls
  | .app f x => .app (applyTermSubstExprWith snapshot f) (applyTermSubstExprWith snapshot x)
  | .lam n ty body bi =>
      let snapshot' := dropTermDbSubstKey snapshot n
      .lam n
        (applyTermSubstExprWith snapshot ty)
        (applyTermSubstExprWith snapshot' body)
        bi
  | .forallE n ty body bi =>
      let snapshot' := dropTermDbSubstKey snapshot n
      .forallE n
        (applyTermSubstExprWith snapshot ty)
        (applyTermSubstExprWith snapshot' body)
        bi
  | .letE n ty val body nondep =>
      let snapshot' := dropTermDbSubstKey snapshot n
      .letE n
        (applyTermSubstExprWith snapshot ty)
        (applyTermSubstExprWith snapshot val)
        (applyTermSubstExprWith snapshot' body)
        nondep
  | .mdata md body => .mdata md (applyTermSubstExprWith snapshot body)
  | .proj s i body => .proj s i (applyTermSubstExprWith snapshot body)
  | e => e

def applyTermSubstExpr (sigma : TermSubst) (e : DbExpr) : DbExpr :=
  applyTermSubstExprWith (termSubstSnapshot sigma) e

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

structure InstTypePremises (k : KernelState) (theta : TypeSubst) (s : Sequent) : Prop where
  validSubst : valid_ty_subst theta
  admissibleImage : admissible_ty_image k.T theta
  typingPreserved : typing_preserved_under_ty_subst theta s
  defCoherent : def_inst_coherent theta s
  constInstance : const_instance_ok theta s
  structurePreserved : theorem_structure_preserved theta s

theorem instTypeFailure_none_of_premises
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hPrem : InstTypePremises k theta s) :
    instTypeFailure k theta s = none := by
  rcases hPrem with ⟨h1, h2, h3, h4, h5, h6⟩
  unfold instTypeFailure
  classical
  simp [h1, h2, h3, h4, h5, h6]

theorem instTypeFailure_invalidSubstitution
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hInvalid : ¬ valid_ty_subst theta) :
    instTypeFailure k theta s = some .invalidSubstitution := by
  unfold instTypeFailure
  classical
  simp [hInvalid]

theorem instTypeFailure_inadmissibleTypeTarget
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hValid : valid_ty_subst theta)
    (hInadmissible : ¬ admissible_ty_image k.T theta) :
    instTypeFailure k theta s = some .inadmissibleTypeTarget := by
  unfold instTypeFailure
  classical
  simp [hValid, hInadmissible]

theorem instTypeFailure_typingFailure
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hValid : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : ¬ typing_preserved_under_ty_subst theta s) :
    instTypeFailure k theta s = some .typingFailure := by
  unfold instTypeFailure
  classical
  simp [hValid, hImg, hTyping]

theorem instTypeFailure_definitionalCoherenceViolation
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hValid : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : ¬ def_inst_coherent theta s) :
    instTypeFailure k theta s = some .definitionalCoherenceViolation := by
  unfold instTypeFailure
  classical
  simp [hValid, hImg, hTyping, hDef]

theorem instTypeFailure_constantInstanceMismatch
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hValid : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : def_inst_coherent theta s)
    (hConst : ¬ const_instance_ok theta s) :
    instTypeFailure k theta s = some .constantInstanceMismatch := by
  unfold instTypeFailure
  classical
  simp [hValid, hImg, hTyping, hDef, hConst]

theorem instTypeFailure_malformedTheoremStructure
    (k : KernelState)
    (theta : TypeSubst)
    (s : Sequent)
    (hValid : valid_ty_subst theta)
    (hImg : admissible_ty_image k.T theta)
    (hTyping : typing_preserved_under_ty_subst theta s)
    (hDef : def_inst_coherent theta s)
    (hConst : const_instance_ok theta s)
    (hStruct : ¬ theorem_structure_preserved theta s) :
    instTypeFailure k theta s = some .malformedTheoremStructure := by
  unfold instTypeFailure
  classical
  simp [hValid, hImg, hTyping, hDef, hConst, hStruct]

inductive Derivable (k : KernelState) : Sequent -> Prop where
  | refl (t : DbExpr) :
      Derivable k { hyps := [], concl := mkEqExpr t t }
  | assume (p : DbExpr) :
      IsBoolExpr p ->
      alphaMember p [p] ->
      Derivable k { hyps := [p], concl := p }
  | trans (A B : Sequent) (x y y' z : DbExpr) :
      A.concl = mkEqExpr x y ->
      B.concl = mkEqExpr y' z ->
      AlphaEqExpr y y' ->
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := alphaUnion A.hyps B.hyps, concl := mkEqExpr x z }
  | mkComb (A B : Sequent) (f g x y : DbExpr) :
      A.concl = mkEqExpr f g ->
      B.concl = mkEqExpr x y ->
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := alphaUnion A.hyps B.hyps, concl := mkCombEqExpr f g x y }
  | abs (A : Sequent) (n : Lean.Name) (ty s t : DbExpr) :
      A.concl = mkEqExpr s t ->
      (∀ h, h ∈ A.hyps -> ¬ dbHasLooseBVar h 0) ->
      Derivable k A ->
      Derivable k { hyps := A.hyps, concl := mkAbsEqExpr n ty s t }
  | beta (r : TypedBetaRedex) :
      betaBinderAgreement r ->
      Derivable k { hyps := [], concl := mkEqExpr (betaRedexExpr r) (typedBetaContract r) }
  | eqMp (A B : Sequent) (p q p' : DbExpr) :
      A.concl = mkEqExpr p q ->
      AlphaEqExpr p p' ->
      B.concl = p' ->
      IsBoolExpr p ->
      Derivable k A -> Derivable k B ->
      Derivable k { hyps := alphaUnion A.hyps B.hyps, concl := q }
  | deductAntisym (A B : Sequent) :
      alphaAssumptionEq
        (alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl))
        (alphaUnion A.hyps B.hyps) ->
      Derivable k A -> Derivable k B ->
      Derivable k
        { hyps := alphaUnion (alphaRemove A.hyps B.concl) (alphaRemove B.hyps A.concl)
        , concl := mkEqExpr A.concl B.concl
        }
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
