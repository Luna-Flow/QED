# research_rewrite design

The `research_rewrite` package explores how QED could offer rewriting and simplification without giving up the kernel-first discipline. It is research-only: it is not used by the shipped packages, and the review recorded in `research/rewrite-simplify/` decided not to promote it on the audited baseline. This page describes the model it implements and the constraints any promotion would have to meet.

## Design goal

Rewriting replaces a subterm by an equal one. In an LCF system every such replacement must be justified by an equation theorem, so a rewriter is really a producer of theorems $\vdash t = t'$. The prototype tests whether that can be done for QED's goals with a small, auditable set of witnesses, and whether the steps can be recorded so that a later stage can check them again.

## Mathematical background

### Conversions and congruence

A *conversion* maps a term $t$ to a theorem $\Gamma \vdash t = t'$. Rewriting at a position inside a larger term needs congruence: if $\Gamma \vdash l = r$, then for every context $C[\cdot]$

$$
\Gamma \vdash C[l] = C[r].
$$

For a context made only of applications this follows by induction on the path to the hole, one MK_COMB per step:

$$
\frac{\vdash f = f \quad \Gamma \vdash l = r}{\Gamma \vdash f\,l = f\,r}\;\textsf{MK\_COMB}
\qquad
\frac{\Gamma \vdash l = r \quad \vdash a = a}{\Gamma \vdash l\,a = r\,a}\;\textsf{MK\_COMB}
$$

with REFL supplying the unchanged side. This is what a path of `CombFun` and `CombArg` site steps produces, recorded as one `Congruence` step per site step. Under an abstraction the step would be ABS, which requires that the bound variable not occur free in $\Gamma$; with a local hypothesis as witness that side condition can fail, and the prototype does not support `AbsBody` sites.

### Witnesses

The equation $l = r$ at the focus comes from one of four witnesses:

| Witness | Theorem | Recorded steps |
| --- | --- | --- |
| `LocalEquality(h)` | $\{l = r\} \vdash l = r$ by ASSUME | `ResolveWitness` |
| `ExplicitTheorem(th)` | the given theorem | `ResolveWitness` |
| `CanonicalUnfold(k)` | the connective's definition applied to its arguments and β-normalised | `Unfold`, `BetaNormalize` |
| `BetaNormalization` | REFL followed by BETA and TRANS steps | `BetaNormalize` |

Right-to-left rewriting with an equation adds `Symmetry`. A rewrite with a local equality carries that equation as a hypothesis, so it is only valid in a goal where the equation is a hypothesis; replaying it without the local fails, as the tutorial shows.

### Using a rewrite in a proof

To turn a rewritten goal back into a proof of the original, one needs $\Gamma \vdash C[l] = C[r]$ and a proof of $C[r]$; EQ_MP with the symmetric equation then proves $C[l]$:

$$
\frac{\Gamma \vdash C[r] = C[l] \qquad \Delta \vdash C[r]}{\Gamma \cup \Delta \vdash C[l]}\;\textsf{EQ\_MP}
$$

The prototype builds the equation internally but does not expose it, and no tactic performs this last step. That is the main reason it is not part of the shipped path.

## Design decisions

### Record obligations, rebuild to check

**Choice.** A rewrite returns the new conclusion and a `ReplayObligation`: the request, the before and after conclusions, and the kinds of kernel steps used. `research_validate_replay_obligation` checks an obligation by rebuilding every segment from its request with kernel rules and comparing the result.

**Why.** Obligations are plain data that can be stored, compared and reviewed, as the promotion gates of the research line require. Because checking rebuilds instead of trusting the record, a forged or stale obligation is rejected.

### Honest failure

Every unsupported case returns `HonestFailure` with a reason: non-boolean conclusions, `AbsBody` sites, folding a definition, β-expansion, unknown locals, witnesses that do not match the focus, and exceeding the step limit. Nothing degrades into a silent no-op except the explicit `NoChange`, which means that no rule applied.

### Bounded simplification

`research_simplify_term_concl` alternates unfolding, β-normalisation and the user's requests until a fixed point, and stops with a failure when the number of segments would exceed `step_limit`. The bound makes termination a property of the configuration rather than of the rule set.

## Correctness and invariants

- **No authority.** Every equation the package builds comes from kernel and `logic` functions, and no theorem leaves the package.
- **Checkable records.** An obligation validates exactly when every segment can be rebuilt from its request against the given state, prelude and locals, and the segments chain from `before_concl` to `after_concl`.
- **Termination.** Simplification performs at most `step_limit` segments.

## Alternatives rejected

- **Returning theorems directly.** It would make the prototype a de facto tactic without the review the research process requires.
- **Rewriting under binders with renaming.** It needs the ABS side condition to be managed and was left out of the evaluated scope.

## Boundaries

- Research-only, not shipped, not imported by any other package, and not reachable from theorem scripts or the command-line tool.
- No rewriting under abstractions, no folding of definitions, no β-expansion.
- No proof of the original goal: the package returns terms and obligations, not theorems.
- The authoritative status of this line is `research/README.md` and the documents in `research/rewrite-simplify/`, not this page.
