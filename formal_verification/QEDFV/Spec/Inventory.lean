namespace QEDFV

inductive ItemKind where
  | definition
  | ruleSchema
  | sideCondition
  | lemma
  | proposition
  | theorem
  | invariant
  | constraint
  | axiomSchema
  | engineeringMap
deriving Repr, BEq

structure SpecItem where
  id : String
  kind : ItemKind
  sourceSection : String
  summary : String
deriving Repr, BEq

def explicitItems : List SpecItem :=
  [ { id := "SEC1_NOTATION_BASELINE", kind := .definition, sourceSection := "Notation", summary := "Object/boundary/meta layering" }
  , { id := "SEC4_SIG_TYPES", kind := .definition, sourceSection := "Foundational Theory", summary := "Type signature and arity" }
  , { id := "SEC4_SIG_CONSTS", kind := .definition, sourceSection := "Foundational Theory", summary := "Constant signature" }
  , { id := "SEC4_RESERVED_BOOL", kind := .constraint, sourceSection := "Foundational Theory", summary := "bool arity 0 reserved" }
  , { id := "SEC4_RESERVED_FUN", kind := .constraint, sourceSection := "Foundational Theory", summary := "fun arity 2 reserved" }
  , { id := "SEC4_RESERVED_IND", kind := .constraint, sourceSection := "Foundational Theory", summary := "ind arity 0 prelude" }
  , { id := "SEC4_CONST_INSTANCE_REL", kind := .definition, sourceSection := "Constant Type Schemes", summary := "instance relation" }
  , { id := "SEC4_RESERVED_EQ", kind := .definition, sourceSection := "Logical Constants", summary := "reserved equality symbol" }
  , { id := "SEC4_RESERVED_CHOICE", kind := .definition, sourceSection := "Logical Constants", summary := "reserved choice symbol" }
  , { id := "SEC4_CHOICE_AXIOM", kind := .axiomSchema, sourceSection := "Logical Constants", summary := "choice axiom schema" }
  , { id := "SEC4_NO_RESERVED_SHADOWING", kind := .constraint, sourceSection := "Logical Constants", summary := "no insertion for reserved names" }
  , { id := "SEC4_TYPED_EQ_FORMATION", kind := .ruleSchema, sourceSection := "Logical Constants", summary := "typed equality formation" }
  , { id := "SEC5_SCOPE_WF", kind := .definition, sourceSection := "Scoped Signature", summary := "scope well-formedness judgment" }
  , { id := "SEC5_SCOPE_LOOKUP", kind := .ruleSchema, sourceSection := "Scoped Signature", summary := "lookup judgment" }
  , { id := "SEC5_SCOPE_PUSH", kind := .ruleSchema, sourceSection := "Scoped Signature", summary := "push judgment" }
  , { id := "SEC5_SCOPE_ADD", kind := .ruleSchema, sourceSection := "Scoped Signature", summary := "add judgment" }
  , { id := "SEC5_SCOPE_POP", kind := .ruleSchema, sourceSection := "Scoped Signature", summary := "pop judgment" }
  , { id := "SEC5_SCOPE_NO_RESERVED", kind := .sideCondition, sourceSection := "Scoped Signature", summary := "frame has no reserved symbol" }
  , { id := "SEC5_SCOPE_DETERMINISTIC", kind := .sideCondition, sourceSection := "Scoped Signature", summary := "deterministic lookup" }
  , { id := "SEC5_GLOBAL_LOCAL_SPLIT", kind := .definition, sourceSection := "Global vs Local", summary := "state split T and S" }
  , { id := "SEC5_DEFHEADS_MONO", kind := .invariant, sourceSection := "Global vs Local", summary := "DefHeads monotonicity" }
  , { id := "SEC5_POP_INVARIANCE", kind := .proposition, sourceSection := "Global vs Local", summary := "pop invariance for DefHeads" }
  , { id := "SEC6_TYPE_GRAMMAR", kind := .definition, sourceSection := "Type Grammar", summary := "type grammar" }
  , { id := "SEC6_TYPEDEF_OK", kind := .definition, sourceSection := "Type Constructor Extension", summary := "TypeDefOK predicate" }
  , { id := "SEC6_TYPEDEF_PRODUCT", kind := .constraint, sourceSection := "Type Constructor Extension", summary := "typedef product contract" }
  , { id := "SEC6_NONEMPTY_INVARIANT", kind := .invariant, sourceSection := "Type Constructor Extension", summary := "no empty type escape" }
  , { id := "SEC6_TERM_GRAMMAR", kind := .definition, sourceSection := "Term Grammar", summary := "term grammar" }
  , { id := "SEC7_ELAB_JUDGMENT", kind := .definition, sourceSection := "Elaboration", summary := "named elaboration" }
  , { id := "SEC7_CORE_TYPING", kind := .definition, sourceSection := "Core Typing", summary := "resolved core typing" }
  , { id := "SEC7_SCOPE_MUTATION_STABILITY", kind := .theorem, sourceSection := "Scope Stability", summary := "typing stability under scope mutation" }
  , { id := "SEC8_TYPE_SUBST", kind := .definition, sourceSection := "Substitution", summary := "type substitution" }
  , { id := "SEC8_TERM_SUBST", kind := .definition, sourceSection := "Substitution", summary := "term substitution" }
  , { id := "SEC8_DEBRUIJN_SHIFT", kind := .definition, sourceSection := "De Bruijn", summary := "typed shift" }
  , { id := "SEC8_DEBRUIJN_SUBST", kind := .definition, sourceSection := "De Bruijn", summary := "typed substitution" }
  , { id := "SEC8_DEBRUIJN_BETA", kind := .ruleSchema, sourceSection := "De Bruijn", summary := "typed beta" }
  , { id := "SEC8_TYPED_CORE_INJECTIVE", kind := .invariant, sourceSection := "De Bruijn", summary := "typed core injectivity" }
  , { id := "SEC8_ALPHA_EQ", kind := .definition, sourceSection := "Alpha-Equivalence", summary := "alpha equivalence and properties" }
  , { id := "SEC9_BOUNDARY_LOWER", kind := .definition, sourceSection := "Boundary Conversion", summary := "term lower function" }
  , { id := "SEC9_BOUNDARY_LIFT", kind := .definition, sourceSection := "Boundary Conversion", summary := "term lift function" }
  , { id := "SEC9_ALPHA_INVARIANT_LOWER", kind := .lemma, sourceSection := "Boundary Conversion", summary := "alpha invariant lowering" }
  , { id := "SEC9_ROUNDTRIP_ALPHA", kind := .lemma, sourceSection := "Boundary Conversion", summary := "roundtrip up to alpha" }
  , { id := "SEC9_LIFT_CONGRUENCE", kind := .lemma, sourceSection := "Boundary Conversion", summary := "lift congruence" }
  , { id := "SEC9_TYPE_SENSITIVE_CORE_MATCH", kind := .lemma, sourceSection := "Boundary Conversion", summary := "type-sensitive core matching" }
  , { id := "SEC9_DENOT_TERM", kind := .lemma, sourceSection := "Boundary Conversion", summary := "term denotation preservation" }
  , { id := "SEC9_DENOT_SEQUENT", kind := .lemma, sourceSection := "Boundary Conversion", summary := "sequent denotation preservation" }
  , { id := "SEC9_RULE_LIFT_SAFETY", kind := .theorem, sourceSection := "Boundary Conversion", summary := "semantic rule lifting safety" }
  , { id := "SEC9_SHADOWING_DETERMINISM", kind := .proposition, sourceSection := "Scoped Shadowing", summary := "shadowing determinism" }
  , { id := "SEC9_OUTER_RESTORE_POP", kind := .proposition, sourceSection := "Scoped Shadowing", summary := "outer restoration by pop" }
  , { id := "SEC9_SCOPE_LOCAL_UNIQUENESS", kind := .proposition, sourceSection := "Scoped Shadowing", summary := "scope-local uniqueness" }
  , { id := "SEC10_THM_OBJECT", kind := .definition, sourceSection := "Theorem Object", summary := "sequent theorem object" }
  , { id := "SEC10_ASSUME_ALPHA_QUOTIENT", kind := .definition, sourceSection := "Theorem Object", summary := "assumptions as alpha quotient" }
  , { id := "SEC11_DEF_RULE", kind := .ruleSchema, sourceSection := "Definitional Extension", summary := "new constant by definition" }
  , { id := "SEC11_DEFOK", kind := .definition, sourceSection := "Definitional Extension", summary := "DefOK" }
  , { id := "SEC11_DEF_THEOREM_SHAPE", kind := .lemma, sourceSection := "Definitional Extension", summary := "generated theorem shape" }
  , { id := "SEC11_NO_GHOST_DRIFT", kind := .lemma, sourceSection := "Definitional Extension", summary := "no ghost drift" }
  , { id := "SEC12_SPECOK", kind := .definition, sourceSection := "Controlled Specification", summary := "SpecOK" }
  , { id := "SEC12_SPEC_DERIVED_RULE", kind := .ruleSchema, sourceSection := "Controlled Specification", summary := "Spec via Choice + DefOK" }
  , { id := "SEC12_SPEC_NO_HIDDEN", kind := .constraint, sourceSection := "Controlled Specification", summary := "no hidden side conditions" }
  , { id := "SEC12_SPEC_CONSERVATIVE", kind := .theorem, sourceSection := "Controlled Specification", summary := "spec conservativity target" }
  , { id := "SEC13_GLOBAL_ENVELOPE", kind := .definition, sourceSection := "Admissibility Envelope", summary := "global admissibility envelope" }
  , { id := "SEC14_RULE_REFL", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "REFL" }
  , { id := "SEC14_RULE_ASSUME", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "ASSUME" }
  , { id := "SEC14_RULE_TRANS", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "TRANS" }
  , { id := "SEC14_RULE_MK_COMB", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "MK_COMB" }
  , { id := "SEC14_RULE_ABS", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "ABS" }
  , { id := "SEC14_RULE_BETA", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "BETA" }
  , { id := "SEC14_RULE_EQ_MP", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "EQ_MP" }
  , { id := "SEC14_RULE_DEDUCT", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "DEDUCT_ANTISYM_RULE" }
  , { id := "SEC14_RULE_INST_TYPE", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "INST_TYPE" }
  , { id := "SEC14_RULE_INST", kind := .ruleSchema, sourceSection := "Primitive Rules", summary := "INST" }
  , { id := "SEC15_SOUNDNESS_STRATEGY", kind := .theorem, sourceSection := "Soundness Strategy", summary := "kernel soundness target" }
  , { id := "SEC15_DEP_MAP", kind := .engineeringMap, sourceSection := "Soundness Strategy", summary := "dependency map" }
  , { id := "SEC16_ERROR_TAXONOMY", kind := .definition, sourceSection := "Engineering Correspondence", summary := "error taxonomy" }
  , { id := "SEC16_RULE_MAPPING", kind := .engineeringMap, sourceSection := "Engineering Correspondence", summary := "rule to implementation map" }
  , { id := "APPA_RULE_DEP_MATRIX", kind := .engineeringMap, sourceSection := "Appendix A", summary := "primitive rule dependency matrix" }
  , { id := "APPB_P0_CHECKLIST", kind := .engineeringMap, sourceSection := "Appendix B", summary := "P0 checklist" }
  , { id := "APPC_AUDIT_DEFHEAD", kind := .proposition, sourceSection := "Appendix C", summary := "definition and state audit" }
  , { id := "APPD_AUDIT_TYPEDEF", kind := .proposition, sourceSection := "Appendix D", summary := "type soundness audit" }
  , { id := "APPE_AUDIT_TYPED_DB", kind := .proposition, sourceSection := "Appendix E", summary := "typed de Bruijn audit" }
  , { id := "APPF_AUDIT_SPEC_CHOICE", kind := .proposition, sourceSection := "Appendix F", summary := "spec and choice audit" }
  ]

def explicitItemCount : Nat := explicitItems.length

end QEDFV
