# cmd design

The `cmd` package is the outermost layer of QED: a file-first command-line tool over the `prover`. This page explains why it is deliberately thin, how it maps prover results to text and exit codes, and what it must never do.

## Design goal

- Check a file of theorem scripts with one command and report every theorem.
- Print diagnostics that a person can act on and a script can parse: a fixed first line per theorem and labelled context lines.
- Exit with a status that build systems can use, with a way to tolerate unfinished proofs during development.
- Add no knowledge of logic, terms or tactics beyond what the prover reports.

## Mathematical background

The tool computes a function from a file to a list of outcomes and a status. Writing $o_1, \dots, o_n$ for the outcomes of the theorems of a file, each in $\{\mathsf{ok}, \mathsf{err}, \mathsf{warn}\}$, the exit status is

$$
\mathsf{exit}(o_1, \dots, o_n) =
\begin{cases}
1 & \text{if some } o_i = \mathsf{err} \\
1 & \text{if some } o_i = \mathsf{warn} \text{ and } \texttt{--no-warn} \text{ is not given} \\
0 & \text{otherwise.}
\end{cases}
$$

The status is monotone: adding a failing theorem to a file can only raise it, and `--no-warn` only ever lowers a status caused by warnings. A usage error, an unreadable file or a file that does not parse gives 1 without any per-theorem outcomes.

## Design decisions

### File first

**Problem.** A theorem prover's CLI can be a REPL, a single-goal checker or a file checker.

**Choice.** `qed-cmd` takes exactly one file. Theorems are separated by `qed` lines and checked independently, starting from an empty kernel state with the prelude installed.

**Why.** Files are what users edit, version and pass to CI. Checking each theorem from the same initial state keeps results independent of order, matching the prover's rule that theorems in a file cannot cite each other.

### Thin by rule

**Problem.** A CLI tends to accumulate logic: special cases, its own parsing of goals, its own idea of success.

**Choice.** The tool only parses arguments, reads the file, calls `prove_theorem_file_results_detailed`, converts the results to strings and computes the exit status. [Code governance](../code_governance.md) makes this a rule: `cmd` is the thinnest layer and consumes only stable prover facades.

**Why.** Every claim the tool prints comes from the prover, so the prover's tests and the corpus cover it, and the tool cannot become a second proof engine with different semantics.

### Stable text, structured first

**Problem.** Output must serve both people and tools.

**Choice.** Each theorem starts with one line `ok …`, `error[kind] …` or `warning[unfinished] …`. Context follows on labelled lines (`step:`, `branch:`, `goal:`, `locals:`, `hole:`, `message:`), with fixed markers `<none>` and `<root>` for absent values. The results are built as structured values (`CmdRunResult`) and rendered in one function.

**Why.** A fixed first line is easy to grep; labelled lines are easy to read and parse; building values before rendering lets the tests check the structure and the text separately. The goal and locals are rendered with the kernel's structural printer, so the text shows exactly the term the kernel saw, at the cost of verbosity.

### Warnings are not successes

An unfinished proof is a warning, not an `ok`. By default it makes the run fail, so CI does not accept a file with holes. `--no-warn` exists for work in progress: it changes the exit status only, never the output, so the holes stay visible.

## Correctness and invariants

- **No authority.** The package constructs no theorems and calls no kernel rules; `ok` is printed only for a `ProverItemProved` item, which carries a kernel theorem.
- **Completeness of the report.** Every theorem of a parseable file produces exactly one block, in file order.
- **Exit status** follows the formula above; `cmd_exit_code` is its implementation and is covered by `cmd_wbtest.mbt`.
- **Positions.** Step numbers and branch paths are the prover's, so they agree with the source and with library use.

## Alternatives rejected

- **Stopping at the first error.** Faster, but users would have to fix and rerun once per error.
- **Hiding warnings with `--no-warn`.** A flag that removes output would let holes go unnoticed.
- **Pretty-printing terms in surface syntax.** A printer that re-introduces `∧` and `->` would be a second interpretation of the encodings that could drift from the parser; the structural printer has no such risk.

## Boundaries

- One file per run; no directories, no imports between files, no watch mode.
- No REPL and no editor protocol.
- No options beyond `-d` and `--no-warn`; the prelude is always installed.
- No library use: the package is an executable and cannot be imported. Library users call the [prover](prover.md) directly.
