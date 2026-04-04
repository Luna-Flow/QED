///|
enum MappingCaseKind {
  PositiveCase
  NegativeCase
}

///|
enum MappingDocVisibility {
  PublicExample
  PublicFailureExample
  InternalOnly
}

///|
struct MappingMatrixEntry {
  case_id : String
  kind : MappingCaseKind
  script : String
  catalog_or_failure_label : String
  capability_or_error_label : String
  doc_anchor : String
  doc_visibility : MappingDocVisibility
}

///|
fn mapping_matrix_entries() -> Array[MappingMatrixEntry] {
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
  ]
}

///|
fn mapping_entries_are_unique(entries : Array[MappingMatrixEntry]) -> Bool {
  let seen : Array[String] = []
  for entry in entries {
    let key = match entry.kind {
      PositiveCase => "positive:" + entry.case_id
      NegativeCase => "negative:" + entry.case_id
    }
    if seen.contains(key) {
      return false
    }
    seen.push(key)
  }
  true
}

///|
fn find_positive_case_by_id(case_id : String) -> PositiveCorpusCase? {
  for case in corpus_cases() {
    if case.case_id == case_id {
      return Some(case)
    }
  }
  None
}

///|
fn find_negative_case_by_id(case_id : String) -> NegativeCorpusCase? {
  for case in negative_corpus_cases() {
    if case.case_id == case_id {
      return Some(case)
    }
  }
  None
}

///|
fn mapping_kind_matches(lhs : MappingCaseKind, rhs : MappingCaseKind) -> Bool {
  match (lhs, rhs) {
    (PositiveCase, PositiveCase) => true
    (NegativeCase, NegativeCase) => true
    _ => false
  }
}

///|
fn mapping_visibility_matches(
  lhs : MappingDocVisibility,
  rhs : MappingDocVisibility,
) -> Bool {
  match (lhs, rhs) {
    (PublicExample, PublicExample) => true
    (PublicFailureExample, PublicFailureExample) => true
    (InternalOnly, InternalOnly) => true
    _ => false
  }
}

///|
fn matrix_entry_count(
  entries : Array[MappingMatrixEntry],
  kind : MappingCaseKind,
  case_id : String,
) -> Int {
  let mut out = 0
  for entry in entries {
    if mapping_kind_matches(entry.kind, kind) && entry.case_id == case_id {
      out = out + 1
    }
  }
  out
}

///|
fn has_mapping_entry(
  entries : Array[MappingMatrixEntry],
  kind : MappingCaseKind,
  case_id : String,
  doc_anchor : String,
  doc_visibility : MappingDocVisibility,
) -> Bool {
  entries.any(fn(entry) {
    mapping_kind_matches(entry.kind, kind) &&
    entry.case_id == case_id &&
    entry.doc_anchor == doc_anchor &&
    mapping_visibility_matches(entry.doc_visibility, doc_visibility)
  })
}

///|
test "prover mapping matrix stays aligned with canonical corpora" {
  let entries = mapping_matrix_entries()
  assert_true(mapping_entries_are_unique(entries))

  for case in corpus_cases() {
    assert_eq(matrix_entry_count(entries, PositiveCase, case.case_id), 1)
  }
  for case in negative_corpus_cases() {
    assert_eq(matrix_entry_count(entries, NegativeCase, case.case_id), 1)
  }

  for entry in entries {
    match entry.kind {
      PositiveCase =>
        match find_positive_case_by_id(entry.case_id) {
          Some(case) => {
            assert_eq(entry.script, case.script)
            assert_eq(
              entry.catalog_or_failure_label,
              catalog_label(case.catalog_class),
            )
            assert_eq(
              entry.capability_or_error_label,
              capability_label(case.capability),
            )
            assert_true(
              !mapping_visibility_matches(
                entry.doc_visibility,
                PublicFailureExample,
              ),
            )
          }
          None => panic()
        }
      NegativeCase =>
        match find_negative_case_by_id(entry.case_id) {
          Some(case) => {
            assert_eq(entry.script, case.script)
            assert_eq(
              entry.catalog_or_failure_label,
              negative_failure_class_label(case.failure_class),
            )
            assert_eq(
              entry.capability_or_error_label,
              negative_error_shape_label(case.expected_error),
            )
            assert_true(
              !mapping_visibility_matches(entry.doc_visibility, PublicExample),
            )
          }
          None => panic()
        }
    }
  }
}

///|
test "prover mapping matrix anchors current manual public examples" {
  let entries = mapping_matrix_entries()
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_intro_exact_identity",
      "manual:runnable_examples",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_apply_and_elim_l",
      "manual:runnable_examples",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_left_disjunction",
      "manual:runnable_examples",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_exact_truth",
      "manual:runnable_examples",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_exact_ex_falso",
      "manual:runnable_examples",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_local_shadow_exact_named_theorem",
      "manual:support_matrix",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_exact_imp_refl",
      "manual:support_matrix",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_exact_and_elim_l",
      "manual:support_matrix",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_apply_or_intro_l",
      "manual:support_matrix",
      PublicExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      PositiveCase,
      "pos_split_conjunction",
      "manual:support_matrix",
      PublicExample,
    ),
  )
}

///|
test "prover mapping matrix anchors current manual failure examples" {
  let entries = mapping_matrix_entries()
  assert_true(
    has_mapping_entry(
      entries,
      NegativeCase,
      "neg_exact_or_intro_wrong_mode",
      "manual:failure_matrix",
      PublicFailureExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      NegativeCase,
      "neg_apply_truth_wrong_mode",
      "manual:failure_matrix",
      PublicFailureExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      NegativeCase,
      "neg_local_shadow_truth_is_not_implication",
      "manual:failure_matrix",
      PublicFailureExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      NegativeCase,
      "neg_exact_context_missing",
      "manual:failure_matrix",
      PublicFailureExample,
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      NegativeCase,
      "neg_non_bool_connector_rejected",
      "manual:failure_matrix",
      PublicFailureExample,
    ),
  )
}
