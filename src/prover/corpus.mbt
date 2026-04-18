///|
/// Canonical regression corpus for the shipped prover/cmd surfaces.
/// This is an engineering contract, not a proof-authority surface.
pub enum ScriptLayout {
  InlineSequential
  BlockSequential
  BranchStructured
}

///|
pub fn script_layout_label(layout : ScriptLayout) -> String {
  match layout {
    InlineSequential => "inline_sequential"
    BlockSequential => "block_sequential"
    BranchStructured => "branch_structured"
  }
}

///|
pub enum PositiveCatalogClass {
  LocalFact
  DirectClose
  ImplicationBacked
  ContextDerived
  StructuralOnly
}

///|
pub enum PositiveTacticCapability {
  IntroExact
  Assumption
  ExactNamedDirectClose
  ExactContextDerived
  ApplyLocalImp
  ApplyNamedImp
  Split
  Left
  Right
  Mixed
}

///|
pub struct PositiveCorpusCase {
  case_id : String
  const_names : Array[String]
  expected_goal : String
  script : String
  layout : ScriptLayout
  catalog_class : PositiveCatalogClass
  capability : PositiveTacticCapability
}

///|
pub fn catalog_label(cls : PositiveCatalogClass) -> String {
  match cls {
    LocalFact => "local_fact"
    DirectClose => "direct_close"
    ImplicationBacked => "implication_backed"
    ContextDerived => "context_derived"
    StructuralOnly => "structural_only"
  }
}

///|
pub fn capability_label(cap : PositiveTacticCapability) -> String {
  match cap {
    IntroExact => "intro_exact"
    Assumption => "assumption"
    ExactNamedDirectClose => "exact_named_direct_close"
    ExactContextDerived => "exact_context_derived"
    ApplyLocalImp => "apply_local_imp"
    ApplyNamedImp => "apply_named_imp"
    Split => "split"
    Left => "left"
    Right => "right"
    Mixed => "mixed"
  }
}

///|
pub fn positive_corpus_cases() -> Array[PositiveCorpusCase] {
  [
    PositiveCorpusCase::{
      case_id: "pos_intro_exact_identity",
      const_names: ["P"],
      expected_goal: "⊢ P -> P",
      script: "theorem pos_intro_exact_identity : ⊢ P -> P := by intro h; exact h",
      layout: InlineSequential,
      catalog_class: LocalFact,
      capability: IntroExact,
    },
    PositiveCorpusCase::{
      case_id: "pos_assumption_hypothesis",
      const_names: ["P"],
      expected_goal: "P ⊢ P",
      script: "theorem pos_assumption_hypothesis : P ⊢ P := by assumption",
      layout: InlineSequential,
      catalog_class: StructuralOnly,
      capability: Assumption,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_local_implication",
      const_names: ["P", "Q"],
      expected_goal: "⊢ (Q -> P) -> Q -> P",
      script: "theorem pos_apply_local_implication : ⊢ (Q -> P) -> Q -> P := by intro himp; intro hq; apply himp; exact hq",
      layout: InlineSequential,
      catalog_class: LocalFact,
      capability: ApplyLocalImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_local_shadow_exact_named_theorem",
      const_names: ["P"],
      expected_goal: "⊢ P -> P",
      script: "theorem pos_local_shadow_exact_named_theorem : ⊢ P -> P := by intro imp_refl; exact imp_refl",
      layout: InlineSequential,
      catalog_class: LocalFact,
      capability: Mixed,
    },
    PositiveCorpusCase::{
      case_id: "pos_local_shadow_apply_named_theorem",
      const_names: ["P", "Q"],
      expected_goal: "⊢ (Q -> P) -> Q -> P",
      script: "theorem pos_local_shadow_apply_named_theorem : ⊢ (Q -> P) -> Q -> P := by intro and_elim_l; intro hq; apply and_elim_l; exact hq",
      layout: InlineSequential,
      catalog_class: LocalFact,
      capability: Mixed,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_imp_refl",
      const_names: ["P"],
      expected_goal: "⊢ P -> P",
      script: "theorem pos_exact_imp_refl : ⊢ P -> P := by exact imp_refl",
      layout: InlineSequential,
      catalog_class: DirectClose,
      capability: ExactNamedDirectClose,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_truth",
      const_names: [],
      expected_goal: "⊢ T",
      script: "theorem pos_exact_truth : ⊢ T := by exact truth",
      layout: InlineSequential,
      catalog_class: DirectClose,
      capability: ExactNamedDirectClose,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_and_elim_l",
      const_names: ["P", "Q"],
      expected_goal: "P ∧ Q ⊢ P",
      script: "theorem pos_exact_and_elim_l : P ∧ Q ⊢ P := by exact and_elim_l",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_and_elim_r",
      const_names: ["P", "Q"],
      expected_goal: "P ∧ Q ⊢ Q",
      script: "theorem pos_exact_and_elim_r : P ∧ Q ⊢ Q := by exact and_elim_r",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_and_intro",
      const_names: ["P", "Q"],
      expected_goal: "P, Q ⊢ P ∧ Q",
      script: "theorem pos_exact_and_intro : P, Q ⊢ P ∧ Q := by exact and_intro",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_not_elim",
      const_names: ["P"],
      expected_goal: "¬ P, P ⊢ F",
      script: "theorem pos_exact_not_elim : ¬ P, P ⊢ F := by exact not_elim",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_ex_falso",
      const_names: ["Q"],
      expected_goal: "F ⊢ Q",
      script: "theorem pos_exact_ex_falso : F ⊢ Q := by exact ex_falso",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_imp_elim",
      const_names: ["P", "Q"],
      expected_goal: "P -> Q, P ⊢ Q",
      script: "theorem pos_exact_imp_elim : P -> Q, P ⊢ Q := by exact imp_elim",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_eq_refl",
      const_names: ["P"],
      expected_goal: "⊢ P = P",
      script: "theorem pos_exact_eq_refl : ⊢ P = P := by exact eq_refl",
      layout: InlineSequential,
      catalog_class: DirectClose,
      capability: ExactNamedDirectClose,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_eq_sym",
      const_names: ["P", "Q"],
      expected_goal: "Q = P ⊢ P = Q",
      script: "theorem pos_exact_eq_sym : Q = P ⊢ P = Q := by exact eq_sym",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_exact_eq_mp",
      const_names: ["P", "Q"],
      expected_goal: "P = Q, P ⊢ Q",
      script: "theorem pos_exact_eq_mp : P = Q, P ⊢ Q := by exact eq_mp",
      layout: InlineSequential,
      catalog_class: ContextDerived,
      capability: ExactContextDerived,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_and_elim_l",
      const_names: ["P", "Q"],
      expected_goal: "⊢ P ∧ Q -> P",
      script: "theorem pos_apply_and_elim_l : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h",
      layout: InlineSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_and_elim_r",
      const_names: ["P", "Q"],
      expected_goal: "⊢ P ∧ Q -> Q",
      script: "theorem pos_apply_and_elim_r : ⊢ P ∧ Q -> Q := by intro h; apply and_elim_r; exact h",
      layout: InlineSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_or_intro_l",
      const_names: ["P", "Q"],
      expected_goal: "⊢ P -> P ∨ Q",
      script: "theorem pos_apply_or_intro_l : ⊢ P -> P ∨ Q := by intro h; apply or_intro_l; exact h",
      layout: InlineSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_or_intro_r",
      const_names: ["P", "Q"],
      expected_goal: "⊢ Q -> P ∨ Q",
      script: "theorem pos_apply_or_intro_r : ⊢ Q -> P ∨ Q := by intro h; apply or_intro_r; exact h",
      layout: InlineSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_apply_eq_sym",
      const_names: ["P", "Q"],
      expected_goal: "⊢ (Q = P) -> P = Q",
      script: "theorem pos_apply_eq_sym : ⊢ (Q = P) -> P = Q := by intro h; apply eq_sym; exact h",
      layout: InlineSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_split_conjunction",
      const_names: ["P", "Q"],
      expected_goal: "P, Q ⊢ P ∧ Q",
      script: "theorem pos_split_conjunction : P, Q ⊢ P ∧ Q := by split; assumption; assumption",
      layout: InlineSequential,
      catalog_class: StructuralOnly,
      capability: Split,
    },
    PositiveCorpusCase::{
      case_id: "pos_left_disjunction",
      const_names: ["P", "Q"],
      expected_goal: "P ⊢ P ∨ Q",
      script: "theorem pos_left_disjunction : P ⊢ P ∨ Q := by left; assumption",
      layout: InlineSequential,
      catalog_class: StructuralOnly,
      capability: Left,
    },
    PositiveCorpusCase::{
      case_id: "pos_right_disjunction",
      const_names: ["P", "Q"],
      expected_goal: "Q ⊢ P ∨ Q",
      script: "theorem pos_right_disjunction : Q ⊢ P ∨ Q := by right; assumption",
      layout: InlineSequential,
      catalog_class: StructuralOnly,
      capability: Right,
    },
    PositiveCorpusCase::{
      case_id: "pos_block_exact_truth",
      const_names: [],
      expected_goal: "⊢ T",
      script: "theorem pos_block_exact_truth : ⊢ T := by\n  exact truth",
      layout: BlockSequential,
      catalog_class: DirectClose,
      capability: ExactNamedDirectClose,
    },
    PositiveCorpusCase::{
      case_id: "pos_block_apply_or_intro_l",
      const_names: ["P", "Q"],
      expected_goal: "⊢ P -> P ∨ Q",
      script: "theorem pos_block_apply_or_intro_l : ⊢ P -> P ∨ Q := by\n  intro h;\n  apply or_intro_l\n  exact h",
      layout: BlockSequential,
      catalog_class: ImplicationBacked,
      capability: ApplyNamedImp,
    },
    PositiveCorpusCase::{
      case_id: "pos_branch_split_conjunction",
      const_names: ["P", "Q"],
      expected_goal: "P, Q ⊢ P ∧ Q",
      script: "theorem pos_branch_split_conjunction : P, Q ⊢ P ∧ Q := by split { assumption } { assumption }",
      layout: BranchStructured,
      catalog_class: StructuralOnly,
      capability: Split,
    },
    PositiveCorpusCase::{
      case_id: "pos_branch_left_disjunction",
      const_names: ["P", "Q"],
      expected_goal: "P ⊢ P ∨ Q",
      script: "theorem pos_branch_left_disjunction : P ⊢ P ∨ Q := by left { assumption }",
      layout: BranchStructured,
      catalog_class: StructuralOnly,
      capability: Left,
    },
  ]
}

///|
pub enum NegativeFailureClass {
  FailureUnknownName
  FailureWrongModeTheoremUsage
  FailureGoalShapeMismatch
  FailureNonBoolConnector
  FailureUnsupportedHonestFailure
  FailureShadowingOrScopeDrift
}

///|
pub enum NegativeErrorShape {
  ErrorTacticUnknownName
  ErrorTacticApplyMismatch
  ErrorTacticGoalShapeMismatch
  ErrorTacticUnsolvedGoals
  ErrorLogicNotBoolTerm
}

///|
pub struct NegativeCorpusCase {
  case_id : String
  bool_consts : Array[String]
  unary_bool_consts : Array[String]
  binary_bool_consts : Array[String]
  script : String
  layout : ScriptLayout
  failure_class : NegativeFailureClass
  expected_error : NegativeErrorShape
}

///|
pub fn negative_failure_class_label(cls : NegativeFailureClass) -> String {
  match cls {
    FailureUnknownName => "unknown_name"
    FailureWrongModeTheoremUsage => "wrong_mode_theorem_usage"
    FailureGoalShapeMismatch => "goal_shape_mismatch"
    FailureNonBoolConnector => "non_bool_connector"
    FailureUnsupportedHonestFailure => "unsupported_honest_failure"
    FailureShadowingOrScopeDrift => "shadowing_or_scope_drift"
  }
}

///|
pub fn negative_error_shape_label(shape : NegativeErrorShape) -> String {
  match shape {
    ErrorTacticUnknownName => "tactic_unknown_name"
    ErrorTacticApplyMismatch => "tactic_apply_mismatch"
    ErrorTacticGoalShapeMismatch => "tactic_goal_shape_mismatch"
    ErrorTacticUnsolvedGoals => "tactic_unsolved_goals"
    ErrorLogicNotBoolTerm => "logic_not_bool_term"
  }
}

///|
pub fn negative_corpus_cases() -> Array[NegativeCorpusCase] {
  [
    NegativeCorpusCase::{
      case_id: "neg_unknown_exact_name",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unknown_exact_name : ⊢ P -> P := by exact missing",
      layout: InlineSequential,
      failure_class: FailureUnknownName,
      expected_error: ErrorTacticUnknownName,
    },
    NegativeCorpusCase::{
      case_id: "neg_unknown_apply_name",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unknown_apply_name : ⊢ P := by apply missing",
      layout: InlineSequential,
      failure_class: FailureUnknownName,
      expected_error: ErrorTacticUnknownName,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_truth_wrong_mode",
      bool_consts: [],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_truth_wrong_mode : ⊢ T := by apply truth",
      layout: InlineSequential,
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_ex_falso_wrong_mode",
      bool_consts: ["Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_ex_falso_wrong_mode : F ⊢ Q := by apply ex_falso",
      layout: InlineSequential,
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_exact_or_intro_wrong_mode",
      bool_consts: ["P", "Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_exact_or_intro_wrong_mode : ⊢ P -> P ∨ Q := by exact or_intro_l",
      layout: InlineSequential,
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_eq_refl_wrong_mode",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_eq_refl_wrong_mode : ⊢ P = P := by apply eq_refl",
      layout: InlineSequential,
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_apply_and_elim_goal_mismatch",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_apply_and_elim_goal_mismatch : ⊢ P := by apply and_elim_l",
      layout: InlineSequential,
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_intro_non_implication_goal",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_intro_non_implication_goal : ⊢ P := by intro h",
      layout: InlineSequential,
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_exact_context_missing",
      bool_consts: ["P", "Q"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_exact_context_missing : P ⊢ P := by exact and_elim_l",
      layout: InlineSequential,
      failure_class: FailureGoalShapeMismatch,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_non_bool_connector_rejected",
      bool_consts: ["Q"],
      unary_bool_consts: ["f"],
      binary_bool_consts: [],
      script: "theorem neg_non_bool_connector_rejected : ⊢ f ∧ Q := by exact truth",
      layout: InlineSequential,
      failure_class: FailureNonBoolConnector,
      expected_error: ErrorLogicNotBoolTerm,
    },
    NegativeCorpusCase::{
      case_id: "neg_unsolved_script_is_honest_failure",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_unsolved_script_is_honest_failure : ⊢ P -> P := by intro h",
      layout: InlineSequential,
      failure_class: FailureUnsupportedHonestFailure,
      expected_error: ErrorTacticUnsolvedGoals,
    },
    NegativeCorpusCase::{
      case_id: "neg_ordinary_imp_not_trusted",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: ["my_imp"],
      script: "theorem neg_ordinary_imp_not_trusted : ⊢ my_imp P P := by intro h; exact h",
      layout: InlineSequential,
      failure_class: FailureUnsupportedHonestFailure,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_local_shadow_truth_is_not_implication",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_local_shadow_truth_is_not_implication : ⊢ P -> P := by intro truth; apply truth",
      layout: InlineSequential,
      failure_class: FailureShadowingOrScopeDrift,
      expected_error: ErrorTacticApplyMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_local_shadow_truth_is_not_direct_witness",
      bool_consts: ["P"],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_local_shadow_truth_is_not_direct_witness : ⊢ P -> T := by intro truth; exact truth",
      layout: InlineSequential,
      failure_class: FailureShadowingOrScopeDrift,
      expected_error: ErrorTacticGoalShapeMismatch,
    },
    NegativeCorpusCase::{
      case_id: "neg_block_apply_truth_wrong_mode",
      bool_consts: [],
      unary_bool_consts: [],
      binary_bool_consts: [],
      script: "theorem neg_block_apply_truth_wrong_mode : ⊢ T := by\n  apply truth",
      layout: BlockSequential,
      failure_class: FailureWrongModeTheoremUsage,
      expected_error: ErrorTacticApplyMismatch,
    },
  ]
}

///|
pub enum MappingCaseKind {
  PositiveCase
  NegativeCase
}

///|
pub fn mapping_case_positive() -> MappingCaseKind {
  PositiveCase
}

///|
pub fn mapping_case_negative() -> MappingCaseKind {
  NegativeCase
}

///|
pub enum MappingDocVisibility {
  PublicExample
  PublicFailureExample
  InternalOnly
}

///|
pub fn mapping_doc_visibility_public_example() -> MappingDocVisibility {
  PublicExample
}

///|
pub fn mapping_doc_visibility_public_failure_example() -> MappingDocVisibility {
  PublicFailureExample
}

///|
pub fn mapping_doc_visibility_internal_only() -> MappingDocVisibility {
  InternalOnly
}

///|
pub struct MappingMatrixEntry {
  case_id : String
  kind : MappingCaseKind
  script : String
  catalog_or_failure_label : String
  capability_or_error_label : String
  doc_anchor : String
  doc_visibility : MappingDocVisibility
}

///|
pub fn mapping_matrix_entries() -> Array[MappingMatrixEntry] {
  [
    MappingMatrixEntry::{
      case_id: "pos_intro_exact_identity",
      kind: PositiveCase,
      script: "theorem pos_intro_exact_identity : ⊢ P -> P := by intro h; exact h",
      catalog_or_failure_label: "local_fact",
      capability_or_error_label: "intro_exact",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_assumption_hypothesis",
      kind: PositiveCase,
      script: "theorem pos_assumption_hypothesis : P ⊢ P := by assumption",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "assumption",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_local_implication",
      kind: PositiveCase,
      script: "theorem pos_apply_local_implication : ⊢ (Q -> P) -> Q -> P := by intro himp; intro hq; apply himp; exact hq",
      catalog_or_failure_label: "local_fact",
      capability_or_error_label: "apply_local_imp",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_local_shadow_exact_named_theorem",
      kind: PositiveCase,
      script: "theorem pos_local_shadow_exact_named_theorem : ⊢ P -> P := by intro imp_refl; exact imp_refl",
      catalog_or_failure_label: "local_fact",
      capability_or_error_label: "mixed",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_local_shadow_apply_named_theorem",
      kind: PositiveCase,
      script: "theorem pos_local_shadow_apply_named_theorem : ⊢ (Q -> P) -> Q -> P := by intro and_elim_l; intro hq; apply and_elim_l; exact hq",
      catalog_or_failure_label: "local_fact",
      capability_or_error_label: "mixed",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_imp_refl",
      kind: PositiveCase,
      script: "theorem pos_exact_imp_refl : ⊢ P -> P := by exact imp_refl",
      catalog_or_failure_label: "direct_close",
      capability_or_error_label: "exact_named_direct_close",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_truth",
      kind: PositiveCase,
      script: "theorem pos_exact_truth : ⊢ T := by exact truth",
      catalog_or_failure_label: "direct_close",
      capability_or_error_label: "exact_named_direct_close",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_and_elim_l",
      kind: PositiveCase,
      script: "theorem pos_exact_and_elim_l : P ∧ Q ⊢ P := by exact and_elim_l",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_and_elim_r",
      kind: PositiveCase,
      script: "theorem pos_exact_and_elim_r : P ∧ Q ⊢ Q := by exact and_elim_r",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_and_intro",
      kind: PositiveCase,
      script: "theorem pos_exact_and_intro : P, Q ⊢ P ∧ Q := by exact and_intro",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_not_elim",
      kind: PositiveCase,
      script: "theorem pos_exact_not_elim : ¬ P, P ⊢ F := by exact not_elim",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_ex_falso",
      kind: PositiveCase,
      script: "theorem pos_exact_ex_falso : F ⊢ Q := by exact ex_falso",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_imp_elim",
      kind: PositiveCase,
      script: "theorem pos_exact_imp_elim : P -> Q, P ⊢ Q := by exact imp_elim",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_eq_refl",
      kind: PositiveCase,
      script: "theorem pos_exact_eq_refl : ⊢ P = P := by exact eq_refl",
      catalog_or_failure_label: "direct_close",
      capability_or_error_label: "exact_named_direct_close",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_eq_sym",
      kind: PositiveCase,
      script: "theorem pos_exact_eq_sym : Q = P ⊢ P = Q := by exact eq_sym",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_exact_eq_mp",
      kind: PositiveCase,
      script: "theorem pos_exact_eq_mp : P = Q, P ⊢ Q := by exact eq_mp",
      catalog_or_failure_label: "context_derived",
      capability_or_error_label: "exact_context_derived",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_and_elim_l",
      kind: PositiveCase,
      script: "theorem pos_apply_and_elim_l : ⊢ P ∧ Q -> P := by intro h; apply and_elim_l; exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_and_elim_r",
      kind: PositiveCase,
      script: "theorem pos_apply_and_elim_r : ⊢ P ∧ Q -> Q := by intro h; apply and_elim_r; exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_or_intro_l",
      kind: PositiveCase,
      script: "theorem pos_apply_or_intro_l : ⊢ P -> P ∨ Q := by intro h; apply or_intro_l; exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_or_intro_r",
      kind: PositiveCase,
      script: "theorem pos_apply_or_intro_r : ⊢ Q -> P ∨ Q := by intro h; apply or_intro_r; exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_apply_eq_sym",
      kind: PositiveCase,
      script: "theorem pos_apply_eq_sym : ⊢ (Q = P) -> P = Q := by intro h; apply eq_sym; exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_split_conjunction",
      kind: PositiveCase,
      script: "theorem pos_split_conjunction : P, Q ⊢ P ∧ Q := by split; assumption; assumption",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "split",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_left_disjunction",
      kind: PositiveCase,
      script: "theorem pos_left_disjunction : P ⊢ P ∨ Q := by left; assumption",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "left",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_right_disjunction",
      kind: PositiveCase,
      script: "theorem pos_right_disjunction : Q ⊢ P ∨ Q := by right; assumption",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "right",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_block_exact_truth",
      kind: PositiveCase,
      script: "theorem pos_block_exact_truth : ⊢ T := by\n  exact truth",
      catalog_or_failure_label: "direct_close",
      capability_or_error_label: "exact_named_direct_close",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_block_apply_or_intro_l",
      kind: PositiveCase,
      script: "theorem pos_block_apply_or_intro_l : ⊢ P -> P ∨ Q := by\n  intro h;\n  apply or_intro_l\n  exact h",
      catalog_or_failure_label: "implication_backed",
      capability_or_error_label: "apply_named_imp",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "pos_branch_split_conjunction",
      kind: PositiveCase,
      script: "theorem pos_branch_split_conjunction : P, Q ⊢ P ∧ Q := by split { assumption } { assumption }",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "split",
      doc_anchor: "manual:support_matrix",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "pos_branch_left_disjunction",
      kind: PositiveCase,
      script: "theorem pos_branch_left_disjunction : P ⊢ P ∨ Q := by left { assumption }",
      catalog_or_failure_label: "structural_only",
      capability_or_error_label: "left",
      doc_anchor: "manual:runnable_examples",
      doc_visibility: PublicExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_unknown_exact_name",
      kind: NegativeCase,
      script: "theorem neg_unknown_exact_name : ⊢ P -> P := by exact missing",
      catalog_or_failure_label: "unknown_name",
      capability_or_error_label: "tactic_unknown_name",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_unknown_apply_name",
      kind: NegativeCase,
      script: "theorem neg_unknown_apply_name : ⊢ P := by apply missing",
      catalog_or_failure_label: "unknown_name",
      capability_or_error_label: "tactic_unknown_name",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_apply_truth_wrong_mode",
      kind: NegativeCase,
      script: "theorem neg_apply_truth_wrong_mode : ⊢ T := by apply truth",
      catalog_or_failure_label: "wrong_mode_theorem_usage",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "manual:failure_matrix",
      doc_visibility: PublicFailureExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_apply_ex_falso_wrong_mode",
      kind: NegativeCase,
      script: "theorem neg_apply_ex_falso_wrong_mode : F ⊢ Q := by apply ex_falso",
      catalog_or_failure_label: "wrong_mode_theorem_usage",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_exact_or_intro_wrong_mode",
      kind: NegativeCase,
      script: "theorem neg_exact_or_intro_wrong_mode : ⊢ P -> P ∨ Q := by exact or_intro_l",
      catalog_or_failure_label: "wrong_mode_theorem_usage",
      capability_or_error_label: "tactic_goal_shape_mismatch",
      doc_anchor: "manual:failure_matrix",
      doc_visibility: PublicFailureExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_apply_eq_refl_wrong_mode",
      kind: NegativeCase,
      script: "theorem neg_apply_eq_refl_wrong_mode : ⊢ P = P := by apply eq_refl",
      catalog_or_failure_label: "wrong_mode_theorem_usage",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_apply_and_elim_goal_mismatch",
      kind: NegativeCase,
      script: "theorem neg_apply_and_elim_goal_mismatch : ⊢ P := by apply and_elim_l",
      catalog_or_failure_label: "goal_shape_mismatch",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_intro_non_implication_goal",
      kind: NegativeCase,
      script: "theorem neg_intro_non_implication_goal : ⊢ P := by intro h",
      catalog_or_failure_label: "goal_shape_mismatch",
      capability_or_error_label: "tactic_goal_shape_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_exact_context_missing",
      kind: NegativeCase,
      script: "theorem neg_exact_context_missing : P ⊢ P := by exact and_elim_l",
      catalog_or_failure_label: "goal_shape_mismatch",
      capability_or_error_label: "tactic_goal_shape_mismatch",
      doc_anchor: "manual:failure_matrix",
      doc_visibility: PublicFailureExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_non_bool_connector_rejected",
      kind: NegativeCase,
      script: "theorem neg_non_bool_connector_rejected : ⊢ f ∧ Q := by exact truth",
      catalog_or_failure_label: "non_bool_connector",
      capability_or_error_label: "logic_not_bool_term",
      doc_anchor: "manual:failure_matrix",
      doc_visibility: PublicFailureExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_unsolved_script_is_honest_failure",
      kind: NegativeCase,
      script: "theorem neg_unsolved_script_is_honest_failure : ⊢ P -> P := by intro h",
      catalog_or_failure_label: "unsupported_honest_failure",
      capability_or_error_label: "tactic_unsolved_goals",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_ordinary_imp_not_trusted",
      kind: NegativeCase,
      script: "theorem neg_ordinary_imp_not_trusted : ⊢ my_imp P P := by intro h; exact h",
      catalog_or_failure_label: "unsupported_honest_failure",
      capability_or_error_label: "tactic_goal_shape_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_local_shadow_truth_is_not_implication",
      kind: NegativeCase,
      script: "theorem neg_local_shadow_truth_is_not_implication : ⊢ P -> P := by intro truth; apply truth",
      catalog_or_failure_label: "shadowing_or_scope_drift",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "manual:failure_matrix",
      doc_visibility: PublicFailureExample,
    },
    MappingMatrixEntry::{
      case_id: "neg_local_shadow_truth_is_not_direct_witness",
      kind: NegativeCase,
      script: "theorem neg_local_shadow_truth_is_not_direct_witness : ⊢ P -> T := by intro truth; exact truth",
      catalog_or_failure_label: "shadowing_or_scope_drift",
      capability_or_error_label: "tactic_goal_shape_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
    MappingMatrixEntry::{
      case_id: "neg_block_apply_truth_wrong_mode",
      kind: NegativeCase,
      script: "theorem neg_block_apply_truth_wrong_mode : ⊢ T := by\n  apply truth",
      catalog_or_failure_label: "wrong_mode_theorem_usage",
      capability_or_error_label: "tactic_apply_mismatch",
      doc_anchor: "internal_only",
      doc_visibility: InternalOnly,
    },
  ]
}
