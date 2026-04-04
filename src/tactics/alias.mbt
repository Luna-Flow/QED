///|
/// Package-local `using` alias file for non-test sources (`proof_state`, `goal`).
using @kernel {
  type KernelState,
  type Thm,
  type Term,
  type LogicError,
  term_alpha_eq,
  term_logical_eq,
  thm_concl,
  thm_hyps,
}

///|
using @logic {
  type PropPrelude,
  type PropApplyTheoremResolution,
  type PropExactWitness,
  type PropExactWitnessResolution,
  prop_dest_imp,
  prop_dest_and,
  prop_dest_or,
  logic_prop_resolve_apply_theorem,
  logic_prop_resolve_exact_witness,
}

///|
using @logic {
  logic_prop_close_hypothesis,
  logic_prop_ensure_sequent,
  logic_prop_discharge_imp_prefix,
  logic_prop_replay_imp_elim_backward,
  logic_prop_replay_imp_elim_backward_thm,
  logic_prop_merge_conjunction,
  logic_prop_or_wrap_left,
  logic_prop_or_wrap_right,
  logic_beta_nf_bool_term_deep,
  logic_normalize_prop_beta,
}
