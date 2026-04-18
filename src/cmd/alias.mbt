///|
/// Production alias entry for the file-first CLI surface.
/// Keep cmd thin: it should compose prover-facing diagnostics, not learn new
/// kernel or parser authority.
using @kernel {
  type LogicError,
  type Term,
  empty_kernel_state,
  term_to_string,
  thm_concl,
}

///|
using @prover {
  type ProverDiagnosticKind,
  type ProverFailure,
  type ProverLocalHyp,
  type ProverUnfinished,
  prove_theorem_script_detailed,
  prover_options,
}

///|
using @tactics {type Goal, goal_concl, goal_hyps}

///|
using @fs {read_file_to_string}

///|
using @sys {exit}
