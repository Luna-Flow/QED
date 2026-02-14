import QEDFV.Kernel.PrimitiveRules

namespace QEDFV

inductive LogicError where
  | typeMismatch
  | variableCaptured
  | notAnEquality
  | notBoolTerm
  | alphaMismatch
  | invalidInstantiation
  | inadmissibleTypeTarget
  | definitionalCoherenceViolation
  | constantInstanceMismatch
  | malformedTheoremStructure
  | varFreeInHyp
  | notTrivialBetaRedex
  | boundaryFailure
deriving Repr, BEq

def instTypeFailureToLogicError : InstTypeFailure -> LogicError
  | .invalidSubstitution => .invalidInstantiation
  | .inadmissibleTypeTarget => .inadmissibleTypeTarget
  | .typingFailure => .typeMismatch
  | .definitionalCoherenceViolation => .definitionalCoherenceViolation
  | .constantInstanceMismatch => .constantInstanceMismatch
  | .malformedTheoremStructure => .malformedTheoremStructure

theorem inst_type_failure_mapping_sound
    (f : InstTypeFailure) :
    ∃ e : LogicError, instTypeFailureToLogicError f = e := by
  exact ⟨instTypeFailureToLogicError f, rfl⟩

theorem inst_type_failure_mapping_complete :
    (instTypeFailureToLogicError .invalidSubstitution = .invalidInstantiation) ∧
    (instTypeFailureToLogicError .inadmissibleTypeTarget = .inadmissibleTypeTarget) ∧
    (instTypeFailureToLogicError .typingFailure = .typeMismatch) ∧
    (instTypeFailureToLogicError .definitionalCoherenceViolation = .definitionalCoherenceViolation) ∧
    (instTypeFailureToLogicError .constantInstanceMismatch = .constantInstanceMismatch) ∧
    (instTypeFailureToLogicError .malformedTheoremStructure = .malformedTheoremStructure) := by
  simp [instTypeFailureToLogicError]

inductive SigError where
  | duplicateConstName
  | constTypeConflict
  | invalidConstInstance
  | unknownConst
  | scopeUnderflow
  | invalidConstRhs
  | reservedSymbol
  | definitionAlreadyExists
  | definitionNotClosed
  | definitionIsCyclic
  | ghostTypeVariable
  | invalidTypeWitness
  | invalidTypePredicate
  | invalidTypeRepName
  | invalidTypeParams
  | invalidTypeArity
  | typeWitnessArityMismatch
  | typeWitnessPredicateMismatch
  | typeConstructorAlreadyExists
  | typeRepresentationAlreadyExists
  | typeMismatch
  | invalidSpecificationWitness
  | specificationFreshnessViolation
  | specificationTypeVarLeak
  | invalidTypeDefinitionProduct
  | missingInfinityAnchor
deriving Repr, BEq

end QEDFV
