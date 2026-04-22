# QED Prelude Assets

This directory contains runnable theorem assets for the current shipped QED
surface. These are not kernel primitives and are not yet wired into the
current theorem-name catalog or resolver surface.

## Inclusion Rules

Only include theorems that are:

- expressible in the current theorem-script surface;
- honestly provable by the current prover;
- confined to the shipped bool / implication / conjunction / disjunction-intro /
  equality / quantifier-intro fragment.

Do not include:

- `or` elimination / cases-driven theorems;
- `forall` elimination / instantiation-driven theorems;
- arithmetic, sets, reals, topology, algebra, datatype-heavy libraries;
- any theorem that needs new kernel authority.

## Files

- `implication.qed`
  - `imp_id`
  - `imp_truth`
  - `imp_drop_left`
  - `imp_chain`
  - `imp_fork`
  - `imp_diamond`

- `conjunction.qed`
  - `and_dup`
  - `and_comm`
  - `and_left_proj`
  - `and_right_proj`
  - `and_chain_pack`

- `disjunction_intro.qed`
  - `or_intro_left`
  - `or_intro_right`
  - `or_nested_left`
  - `or_nested_right`
  - `pipeline_or_right`
  - `and_plus_or`

- `equality.qed`
  - `eq_refl_bool`
  - `eq_sym_bool`
  - `eq_mp_bool`

- `quantifier_intro.qed`
  - `forall_id`
  - `forall_dup`
  - `binder_id`
  - `binder_or_intro`
  - `forall_chain`

- `mixed.qed`
  - `constructive_diamond`
  - `frame_stress`

## Closest HOL Light Layer

These assets correspond most closely to the early bool-core theorem layer in
HOL Light, not to the larger arithmetic / set / real libraries.
