///|
pub enum PropTheoremClass {
  DirectClose
  ImplicationBacked
  ContextDerived
}

///|
pub struct PropTheoremEntry {
  name : String
  premise_count : Int
  exact_class : PropTheoremClass?
  apply_class : PropTheoremClass?
}

///|
fn prop_theorem_entries() -> Array[PropTheoremEntry] {
  [
    PropTheoremEntry::{
      name: "imp_refl",
      premise_count: 0,
      exact_class: Some(DirectClose),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "truth",
      premise_count: 0,
      exact_class: Some(DirectClose),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "and_elim_l",
      premise_count: 1,
      exact_class: Some(ContextDerived),
      apply_class: Some(ImplicationBacked),
    },
    PropTheoremEntry::{
      name: "and_elim_r",
      premise_count: 1,
      exact_class: Some(ContextDerived),
      apply_class: Some(ImplicationBacked),
    },
    PropTheoremEntry::{
      name: "and_intro",
      premise_count: 2,
      exact_class: Some(ContextDerived),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "not_elim",
      premise_count: 2,
      exact_class: Some(ContextDerived),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "ex_falso",
      premise_count: 1,
      exact_class: Some(ContextDerived),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "or_intro_l",
      premise_count: 1,
      exact_class: None,
      apply_class: Some(ImplicationBacked),
    },
    PropTheoremEntry::{
      name: "or_intro_r",
      premise_count: 1,
      exact_class: None,
      apply_class: Some(ImplicationBacked),
    },
    PropTheoremEntry::{
      name: "imp_elim",
      premise_count: 2,
      exact_class: Some(ContextDerived),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "eq_refl",
      premise_count: 0,
      exact_class: Some(DirectClose),
      apply_class: None,
    },
    PropTheoremEntry::{
      name: "eq_sym",
      premise_count: 1,
      exact_class: Some(ContextDerived),
      apply_class: Some(ImplicationBacked),
    },
    PropTheoremEntry::{
      name: "eq_mp",
      premise_count: 2,
      exact_class: Some(ContextDerived),
      apply_class: None,
    },
  ]
}

///|
pub fn logic_prop_theorem_count() -> Int {
  prop_theorem_entries().length()
}

///|
pub fn logic_prop_theorem_at(idx : Int) -> PropTheoremEntry? {
  let entries = prop_theorem_entries()
  if idx < 0 || idx >= entries.length() {
    None
  } else {
    Some(entries[idx])
  }
}

///|
pub fn logic_prop_theorem_entry(name : String) -> PropTheoremEntry? {
  for entry in prop_theorem_entries() {
    if entry.name == name {
      return Some(entry)
    }
  }
  None
}
