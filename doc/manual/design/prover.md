# prover design

The `prover` package turns a theorem script into one of three outcomes: a kernel theorem, a structured failure, or an unfinished proof. This page explains that result model, how branch blocks are scheduled on top of the tactics layer, and why the package fails closed: no path through it can report success without a kernel theorem for the stated goal.

## Design goal

- Run theorem scripts end to end: parse, install the prelude, lower the goal, execute steps, schedule branch blocks.
- Tell the user exactly where a proof stops: theorem, step number, branch path, source text, current goal and local hypotheses.
- Never present anything but a kernel `Thm` as a proof. Unsupported input, failing steps and holes are reported as such.
- Keep the documentation honest by publishing the corpus of scripts that the tests run and the manual quotes.

## Mathematical background

### Outcomes as a sum type

For a script with goal $\Gamma \vdash c$ the result is

$$
\mathsf{run}(\mathit{script}) \in \underbrace{\mathsf{Thm}_{\Gamma \vdash c}}_{\texttt{Proved}} \;+\; \underbrace{\mathsf{Failure}}_{\texttt{Failed}} \;+\; \underbrace{\mathsf{Goal} \times \mathsf{Position}}_{\texttt{Unfinished}}
$$

The three cases are disjoint, and only the first carries a theorem. In particular an unfinished proof is not a theorem with an extra assumption: it is a report containing the goal $\Gamma' \vdash c'$ that the hole stands for. Turning the hole into a hypothesis would give the theorem $\Gamma \cup \{c'\} \vdash c$, which is a different statement from the one the user asked for.

### Branch blocks as nested proofs

A step followed by branch blocks, such as `split { s₁ } { s₂ }`, runs the step on the current goal $G$, producing subgoals $G_1, G_2$. Each block $s_i$ is then a separate proof of $G_i$:

$$
\frac{s_1 \text{ proves } G_1 \qquad s_2 \text{ proves } G_2}{\texttt{split}\,\{s_1\}\,\{s_2\} \text{ proves } G}
$$

The prover runs $s_i$ in a fresh proof state rooted at $G_i$ (`ps_isolate_pending_at`), obtains a theorem $t_i$ for $G_i$ from that state, and closes $G_i$ in the parent state with $t_i$. Because the parent's justification for `split` is valid, the theorems compose into a theorem for $G$; this is the LCF composition of justifications described in the [tactics design](tactics.md), applied one level up.

## Design decisions

### Three-way results instead of `Result`

**Problem.** A `Result[Thm, Error]` would force an unfinished proof to be either a theorem, which is false, or an error, which loses the difference between "wrong" and "not done yet".

**Choice.** `ProverRunResult` has three constructors. `prove_theorem_script` still returns a `Result` for callers that only want a theorem, but its error side `ProverScriptError` keeps failures and unfinished proofs apart.

**Why.** Editors and the command-line tool treat the cases differently: an error stops the user, an unfinished proof is a warning with a goal to work on. The specification requires that a hole never produce theorem authority; the type makes that impossible to get wrong.

### Diagnostics carry positions and context

Every failure and unfinished report records the theorem name, the step index, the branch path, the step's span and source text, and the goal and locals at that point, all in terms of the raw input. The `cmd` package prints these fields directly. The cost is a wide record; the benefit is that no consumer has to re-run anything to explain a result.

### Isolated frames for branch blocks

**Problem.** Running branch bodies inside the parent state would let a failure in one branch disturb the bookkeeping of its sibling, and would make the reported branch path depend on scheduling details.

**Choice.** Each branch body runs in its own proof state built from one pending goal, without the parent's replay context. When the body finishes, `ps_close_frame` must return a theorem for that goal; the parent closes the goal with it. A body that leaves goals open is a failure at the branch step.

**Why.** Each block is then an independent proof of its subgoal, which is what the block syntax suggests, and step indices and branch paths are assigned in reading order regardless of nesting.

### Files continue after a bad theorem

**Problem.** A file with several theorems should report all problems, not only the first.

**Choice.** `prove_theorem_file_results_detailed` runs every theorem and returns one item each. Only an unparseable file or a failure to install the prelude fails the whole file. Proved theorems are not added to the state: later theorems cannot cite earlier ones by name.

**Why.** Reporting every theorem is what a user of the CLI expects. Not adding theorems to the state keeps the catalog of citable names fixed, as the [user manual](../manual.md) states; a theorem environment is not part of the shipped subset.

### The prelude is installed by option

With `auto_install_prelude` on, which is the default, the prover installs the propositional prelude before running. Scripts can then use `T`, `F` and catalog theorems without preparing a state. Tests that need a specific state turn it off and install constants themselves.

### The corpus is code

The scripts that the manual and these pages quote are values in `corpus.mbt`: positive, negative, unfinished and quantifier cases, each with an identifier and the capability or failure it shows, and a mapping matrix from case to documentation anchor. The tests run every case and check the mapping, so a published example cannot drift from what the code does. The conformance guide makes this a rule for public examples.

## Correctness and invariants

- **Fail closed.** `Proved` is constructed in one place, from the result of `ps_qed`, which returns a theorem only after the tactics layer checked it against the root goal. Every other path returns `Failed` or `Unfinished`.
- **No authority.** The package calls the parser, the tactics layer and kernel state functions; it does not build theorems itself.
- **Holes do not leak.** A hole stops the script before `ps_qed`; there is no code path that turns an unfinished state into a theorem.
- **Positions are raw.** Offsets and spans in reports refer to the input string as given, through the parser's offset map.
- **Ordering.** Items of a file report are in source order, and step indices count steps in reading order across branch blocks.

## Alternatives rejected

- **Exceptions for failures.** Results keep every outcome visible in the type and let the CLI render all of them uniformly.
- **Holes as assumptions.** Rejected because the resulting theorem would state something other than the goal, as shown above.
- **A shared state for branch bodies.** Simpler to implement, but it couples sibling branches and makes blame depend on scheduling.
- **Theorem environment across a file.** Letting later theorems cite earlier ones needs a naming and replay discipline that the specification does not yet define; until then the catalog is the only source of names.

## Boundaries

- The prover does not add steps; the step set is that of [tactics](tactics.md) plus `hole`.
- It does not read files or print; the [cmd](cmd.md) package does.
- It does not search for proofs, rewrite or simplify. The research prototype in [research_rewrite](research_rewrite.md) is not wired in.
- It does not store proved theorems or let scripts refer to each other.
