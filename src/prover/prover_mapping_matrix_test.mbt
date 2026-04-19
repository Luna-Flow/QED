///|
fn mapping_entries_are_unique(entries : Array[MappingMatrixEntry]) -> Bool {
  let seen : Array[String] = []
  for entry in entries {
    let key = mapping_kind_label(entry.kind) + ":" + entry.case_id
    if seen.contains(key) {
      return false
    }
    seen.push(key)
  }
  true
}

///|
fn find_positive_case_by_id(case_id : String) -> PositiveCorpusCase? {
  for case in positive_corpus_cases() {
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
fn find_unfinished_case_by_id(case_id : String) -> UnfinishedCorpusCase? {
  for case in unfinished_corpus_cases() {
    if case.case_id == case_id {
      return Some(case)
    }
  }
  None
}

///|
fn find_quantifier_case_by_id(case_id : String) -> QuantifierCorpusCase? {
  for case in quantifier_corpus_cases() {
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
    (UnfinishedCase, UnfinishedCase) => true
    _ => false
  }
}

///|
fn mapping_kind_label(kind : MappingCaseKind) -> String {
  match kind {
    PositiveCase => "positive"
    NegativeCase => "negative"
    UnfinishedCase => "unfinished"
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

  for case in positive_corpus_cases() {
    assert_eq(
      matrix_entry_count(entries, mapping_case_positive(), case.case_id),
      1,
    )
  }
  for case in negative_corpus_cases() {
    assert_eq(
      matrix_entry_count(entries, mapping_case_negative(), case.case_id),
      1,
    )
  }
  for case in unfinished_corpus_cases() {
    assert_eq(
      matrix_entry_count(entries, mapping_case_unfinished(), case.case_id),
      1,
    )
  }
  for case in quantifier_corpus_cases() {
    assert_eq(matrix_entry_count(entries, case.kind, case.case_id), 1)
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
                mapping_doc_visibility_public_failure_example(),
              ),
            )
          }
          None =>
            match find_quantifier_case_by_id(entry.case_id) {
              Some(case) => {
                assert_true(mapping_kind_matches(entry.kind, case.kind))
                assert_eq(entry.script, case.script)
                assert_eq(entry.catalog_or_failure_label, "quantifier_surface")
                assert_eq(
                  entry.capability_or_error_label,
                  case.capability_label,
                )
                assert_eq(entry.doc_anchor, case.manual_anchor)
                assert_true(
                  mapping_visibility_matches(
                    entry.doc_visibility,
                    mapping_doc_visibility_public_example(),
                  ),
                )
              }
              None => panic()
            }
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
              !mapping_visibility_matches(
                entry.doc_visibility,
                mapping_doc_visibility_public_example(),
              ),
            )
          }
          None =>
            match find_quantifier_case_by_id(entry.case_id) {
              Some(case) => {
                assert_true(mapping_kind_matches(entry.kind, case.kind))
                assert_eq(entry.script, case.script)
                assert_eq(entry.catalog_or_failure_label, "quantifier_surface")
                assert_eq(
                  entry.capability_or_error_label,
                  case.capability_label,
                )
                assert_eq(entry.doc_anchor, case.manual_anchor)
                assert_true(
                  mapping_visibility_matches(
                    entry.doc_visibility,
                    mapping_doc_visibility_public_failure_example(),
                  ),
                )
              }
              None => panic()
            }
        }
      UnfinishedCase =>
        match find_unfinished_case_by_id(entry.case_id) {
          Some(case) => {
            assert_eq(entry.script, case.script)
            assert_eq(entry.catalog_or_failure_label, "unfinished_proof")
            assert_eq(entry.capability_or_error_label, "hole")
            assert_true(
              mapping_visibility_matches(
                entry.doc_visibility,
                mapping_doc_visibility_public_unfinished_example(),
              ),
            )
          }
          None =>
            match find_quantifier_case_by_id(entry.case_id) {
              Some(case) => {
                assert_true(mapping_kind_matches(entry.kind, case.kind))
                assert_eq(entry.script, case.script)
                assert_eq(entry.catalog_or_failure_label, "unfinished_proof")
                assert_eq(
                  entry.capability_or_error_label,
                  case.capability_label,
                )
                assert_eq(entry.doc_anchor, case.manual_anchor)
                assert_true(
                  mapping_visibility_matches(
                    entry.doc_visibility,
                    mapping_doc_visibility_public_unfinished_example(),
                  ),
                )
              }
              None => panic()
            }
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
      mapping_case_positive(),
      "pos_intro_exact_identity",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_apply_and_elim_l",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_left_disjunction",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_branch_left_disjunction",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_unfinished(),
      "unf_hole_intro",
      "manual:unfinished_examples",
      mapping_doc_visibility_public_unfinished_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_unfinished(),
      "unf_nested_branch_hole",
      "manual:unfinished_examples",
      mapping_doc_visibility_public_unfinished_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_exact_truth",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_exact_ex_falso",
      "manual:runnable_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_quant_seq_identity",
      "manual:quantifier_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_quant_branch_split",
      "manual:quantifier_examples",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_unfinished(),
      "unf_quant_nested_branch_hole",
      "manual:quantifier_unfinished_examples",
      mapping_doc_visibility_public_unfinished_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_local_shadow_exact_named_theorem",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_exact_imp_refl",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_exact_and_elim_l",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_apply_or_intro_l",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_split_conjunction",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_positive(),
      "pos_branch_split_conjunction",
      "manual:support_matrix",
      mapping_doc_visibility_public_example(),
    ),
  )
}

///|
test "prover mapping matrix anchors current manual failure examples" {
  let entries = mapping_matrix_entries()
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_exact_or_intro_wrong_mode",
      "manual:failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_apply_truth_wrong_mode",
      "manual:failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_local_shadow_truth_is_not_implication",
      "manual:failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_exact_context_missing",
      "manual:failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_non_bool_connector_rejected",
      "manual:failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
  assert_true(
    has_mapping_entry(
      entries,
      mapping_case_negative(),
      "neg_quant_branch_goal_mismatch",
      "manual:quantifier_failure_matrix",
      mapping_doc_visibility_public_failure_example(),
    ),
  )
}
