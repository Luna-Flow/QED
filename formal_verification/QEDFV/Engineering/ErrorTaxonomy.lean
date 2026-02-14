namespace QEDFV

inductive LogicError where
  | typeMismatch
  | variableCaptured
  | notAnEquality
  | notBoolTerm
  | alphaMismatch
  | invalidInstantiation
  | varFreeInHyp
  | notTrivialBetaRedex
  | boundaryFailure
deriving Repr, BEq

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
