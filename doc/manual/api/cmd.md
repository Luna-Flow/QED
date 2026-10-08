# cmd API

## Purpose

The `cmd` package (`Luna-Flow/QED/cmd`) is the command-line tool `qed-cmd`. It reads one theorem-script file, checks every theorem in it with the `prover` package, prints one report per theorem and exits with a status code. It is an executable package (`pkgtype(kind: "executable")` in its `moon.pkg`), so other packages cannot import it; its public functions are the tested surface of the tool and are listed here for maintainers.

The [cmd tutorial](../tutorial/cmd.md) walks through the tool; the [cmd design](../design/cmd.md) explains its output contract. The full output contract is also in the [user manual](../manual.md).

## Importing

`cmd` is an executable package, so no `moon.pkg` can import it. Run it from the repository with `moon run src/cmd <file>`, or build it and call the `qed-cmd` binary; the [cmd tutorial](../tutorial/cmd.md) shows both. Programs that need the same results as values call the [prover](prover.md) instead.

## Command line

### `qed-cmd`

`qed-cmd` checks a theorem-script file.

```text
qed-cmd [-d] [--no-warn] <file>
```

| Argument | Meaning |
| --- | --- |
| `<file>` | The theorem-script file. Theorems are separated by lines containing `qed`; a file with one theorem may omit it. |
| `-d` | Print the conclusion of each proved theorem after its name. |
| `--no-warn` | Exit with 0 when there are unfinished proofs but no errors. Warnings are still printed. |

From the repository, run it through `moon run`; arguments for the tool follow `--`:

```bash
moon run src/cmd examples/truth_file.qed
moon run src/cmd -- -d --no-warn examples/multi_with_hole.qed
```

An unknown option, a missing file argument or a second file argument prints a usage line and exits with 1.

### Output

Each theorem produces one block, in file order.

| Result | Output |
| --- | --- |
| Proved | `ok <name>`, or `ok <name>: <conclusion>` with `-d` |
| Failed | `error[<kind>] <file> (<name>): <detail>`, followed by `step:`, `branch:`, `goal:` and `locals:` lines when the failure has proof context |
| Unfinished | `warning[unfinished] <file> (<name>): <detail>`, followed by `theorem:`, `step:`, `branch:`, `goal:`, `locals:`, `hole:` and `message:` lines |

`<kind>` is one of `usage`, `io`, `parse`, `bridge`, `tactic`, `sig`, `logic`. A branch path prints as `1.1`, the empty path as `<root>`, and a missing value as `<none>`. Goals and locals are printed with the kernel's structural term printer.

### Exit status

| Status | When |
| --- | --- |
| 0 | Every theorem was proved, or there were only unfinished proofs and `--no-warn` was given. |
| 1 | A usage or I/O error, a file that does not parse, any failed theorem, or an unfinished proof without `--no-warn`. |

## Options

### `CmdOptions`

`CmdOptions` holds the settings of a run: whether to install the propositional prelude, whether to print conclusions, and whether warnings alone should still exit with 0.

```mbti
pub struct CmdOptions {
  auto_install_prelude : Bool
  detailed_success : Bool
  no_warn : Bool
}
```

### `default_cmd_options`, `cmd_options`, `cmd_options_with_detail` and `cmd_options_full`

These functions build options. `default_cmd_options()` installs the prelude and leaves the two flags off; the others set one, two or three fields.

```mbti
pub fn default_cmd_options() -> CmdOptions
pub fn cmd_options(Bool) -> CmdOptions
pub fn cmd_options_with_detail(Bool, Bool) -> CmdOptions
pub fn cmd_options_full(Bool, Bool, Bool) -> CmdOptions
```

## Running

### `cmd_run_argv`

`cmd_run_argv(args, opts)` parses a command line, where `args[0]` is the program name, reads the file and checks it. Flags on the command line override the corresponding fields of `opts`.

```mbti
pub fn cmd_run_argv(Array[String], CmdOptions) -> CmdRunResult
```

### `cmd_run_script`

`cmd_run_script(path, src, opts)` checks the source text `src` as if it had been read from `path`, starting from an empty kernel state.

```mbti
pub fn cmd_run_script(String, String, CmdOptions) -> CmdRunResult
```

### `cmd_render_result` and `cmd_exit_code`

`cmd_render_result` produces the text the tool prints, and `cmd_exit_code` the exit status, as described above.

```mbti
pub fn cmd_render_result(CmdRunResult) -> String
pub fn cmd_exit_code(CmdRunResult) -> Int
```

## Results

### `CmdRunResult`

`CmdRunResult` is a per-theorem report for a file that could be checked, or a single failure (usage, I/O, parse) or unfinished result for the whole run.

```mbti
pub enum CmdRunResult {
  FileReport(CmdFileReport)
  Failure(CmdFailure)
  Unfinished(CmdUnfinished)
}
```

### `CmdFileReport` and `CmdFileItem`

A file report lists one item per theorem and remembers the two output flags.

```mbti
pub struct CmdFileReport {
  path : String
  items : Array[CmdFileItem]
  detailed_success : Bool
  no_warn : Bool
}

pub enum CmdFileItem {
  CmdItemSuccess(CmdSuccess)
  CmdItemFailure(CmdFailure)
  CmdItemWarning(CmdUnfinished)
}
```

### `CmdSuccess`

`CmdSuccess` is a proved theorem: its name, its conclusion and the rendered conclusion.

```mbti
pub struct CmdSuccess {
  path : String
  theorem_name : String
  conclusion : @kernel.Term
  conclusion_summary : String
}
```

### `CmdFailure` and `CmdFailureKind`

`CmdFailure` is a failure with its location and context rendered as strings; `CmdFailureKind` names its origin.

```mbti
pub struct CmdFailure {
  path : String
  theorem_name : String?
  kind : CmdFailureKind
  step_index : Int?
  branch_path : Array[Int]
  current_goal_summary : String?
  local_hyps : Array[CmdLocalHypSummary]
  detail : String
}

pub enum CmdFailureKind {
  Usage
  Io
  Parse
  Bridge
  Tactic
  Sig
  Logic
}
```

### `cmd_failure_kind_to_string`

`cmd_failure_kind_to_string` returns the lower-case kind printed inside `error[...]`.

```mbti
pub fn cmd_failure_kind_to_string(CmdFailureKind) -> String
```

### `CmdUnfinished`, `cmd_unfinished` and `cmd_unfinished_from_prover`

`CmdUnfinished` is an unfinished proof with its context rendered as strings. `cmd_unfinished` builds one as a run result; `cmd_unfinished_from_prover` converts the prover's report.

```mbti
pub struct CmdUnfinished {
  path : String
  theorem_name : String
  step_index : Int?
  branch_path : Array[Int]
  current_goal_summary : String
  local_hyps : Array[CmdLocalHypSummary]
  hole_name : String?
  detail : String
}

pub fn cmd_unfinished(String, String, Int?, Array[Int], String, Array[CmdLocalHypSummary], String?, String) -> CmdRunResult
pub fn cmd_unfinished_from_prover(String, @prover.ProverUnfinished) -> CmdRunResult
```

### `CmdLocalHypSummary`

`CmdLocalHypSummary` is a local hypothesis rendered for output, printed as `name: term`.

```mbti
pub struct CmdLocalHypSummary {
  name : String
  term_summary : String
}
```
