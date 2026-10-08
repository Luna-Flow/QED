# research_rewrite API

The `research_rewrite` package (`Luna-Flow/QED/research_rewrite`) is a research prototype for rewriting and simplifying proof goals. It rewrites the conclusion of a goal at a chosen position, records how each step can be replayed with kernel rules, and can check such a record again. It depends only on `kernel` and `logic`.

> [!IMPORTANT]
> This package is research-only and not shipped. No other package uses it, theorem scripts have no `rewrite` or `simp` step, and the go/no-go review in `research/rewrite-simplify/` concluded "No-Go" for promotion. Its interface may change or disappear.

The [research_rewrite design](../design/research_rewrite.md) explains the replay model, and the [research_rewrite tutorial](../tutorial/research_rewrite.md) runs a rewrite.

## Requests

### `RewriteWitness`, `ConnectorKind` and their constructor functions

`RewriteWitness` says which equation justifies a rewrite: a local hypothesis of the goal by name, an explicit theorem, the definition of a connective, or β-normalisation.

```mbti
pub enum RewriteWitness {
  LocalEquality(String)
  ExplicitTheorem(@kernel.Thm)
  CanonicalUnfold(ConnectorKind)
  BetaNormalization
}

pub enum ConnectorKind {
  Not
  Imp
  And
  Or
}

pub fn research_local_equality(String) -> RewriteWitness
pub fn research_explicit_theorem(@kernel.Thm) -> RewriteWitness
pub fn research_canonical_unfold_not() -> RewriteWitness
pub fn research_canonical_unfold_imp() -> RewriteWitness
pub fn research_canonical_unfold_and() -> RewriteWitness
pub fn research_canonical_unfold_or() -> RewriteWitness
pub fn research_beta_normalization() -> RewriteWitness
```

A local or explicit witness must conclude an equation $l = r$. A connective unfold rewrites an application of the prelude constant to its β-normalised definition.

### `RewriteDirection`, `research_left_to_right` and `research_right_to_left`

`RewriteDirection` says whether to replace $l$ by $r$ or $r$ by $l$.

```mbti
pub enum RewriteDirection {
  LeftToRight
  RightToLeft
}

pub fn research_left_to_right() -> RewriteDirection
pub fn research_right_to_left() -> RewriteDirection
```

Right-to-left is supported for local and explicit witnesses only; folding a definition or β-expanding fails honestly.

### `RewriteSiteStep` and its constructor functions

A site is a path from the root of the conclusion to the subterm to rewrite: into the function or the argument of an application, or into the body of an abstraction.

```mbti
pub enum RewriteSiteStep {
  CombFun
  CombArg
  AbsBody
}

pub fn research_site_comb_fun() -> RewriteSiteStep
pub fn research_site_comb_arg() -> RewriteSiteStep
pub fn research_site_abs_body() -> RewriteSiteStep
```

The empty path is the whole conclusion. Rewriting under an abstraction (`AbsBody`) is not supported and fails honestly.

### `RewriteRequest` and `research_rewrite_request`

A request combines a witness, a direction and a site.

```mbti
pub struct RewriteRequest {
  witness : RewriteWitness
  direction : RewriteDirection
  site : Array[RewriteSiteStep]
}

pub fn research_rewrite_request(RewriteWitness, RewriteDirection, Array[RewriteSiteStep]) -> RewriteRequest
```

## Rewriting

### `research_rewrite_term_concl`

`research_rewrite_term_concl(state, prelude, locals, concl, request)` performs one rewrite of the proposition `concl`. `locals` are the named hypotheses that `LocalEquality` may refer to.

```mbti
pub fn research_rewrite_term_concl(@kernel.KernelState, @logic.PropPrelude, Array[(String, @kernel.Term)], @kernel.Term, RewriteRequest) -> RewriteResult
```

It returns the rewritten conclusion with a replay obligation of one segment, or an honest failure: the conclusion is not a proposition, the site does not exist, the witness is unknown or does not match the subterm at the site, or a kernel step fails.

### `research_simplify_term_concl` and `SimplifyConfig`

`research_simplify_term_concl` rewrites repeatedly until nothing changes: in each round it unfolds a connective if `allow_unfold`, β-normalises if `allow_beta`, and applies each request of `rewrite_requests` that matches. `step_limit` bounds the number of segments.

```mbti
pub struct SimplifyConfig {
  step_limit : Int
  allow_unfold : Bool
  allow_beta : Bool
  rewrite_requests : Array[RewriteRequest]
}

pub fn research_simplify_config(Int, Bool, Bool, Array[RewriteRequest]) -> SimplifyConfig
pub fn research_simplify_term_concl(@kernel.KernelState, @logic.PropPrelude, Array[(String, @kernel.Term)], @kernel.Term, SimplifyConfig) -> RewriteResult
```

It returns `NoChange` when no step applies, and fails honestly with "step limit exceeded" when more than `step_limit` segments would be needed, or with "step limit must be non-negative".

### `RewriteResult`

`RewriteResult` is the outcome of a rewrite or simplification.

```mbti
pub enum RewriteResult {
  Rewritten(@kernel.Term, ReplayObligation)
  NoChange
  HonestFailure(String)
}
```

The result is a term and a record, not a theorem: nothing here proves the rewritten goal.

## Replay obligations

### `ReplayStepKind` and `research_step_name`

`ReplayStepKind` names the kernel-level steps a segment needs: resolving the witness, symmetry, congruence (one per site step), unfolding a definition, β-normalisation. `research_step_name` returns the constructor name as a string.

```mbti
pub enum ReplayStepKind {
  ResolveWitness
  Symmetry
  Congruence
  Unfold
  BetaNormalize
}

pub fn research_step_name(ReplayStepKind) -> String
```

### `ReplaySegment`, `ReplayObligation` and their constructor functions

A segment records one rewrite: the request, the conclusion before and after, and its steps. An obligation chains segments from a first conclusion to a last.

```mbti
pub struct ReplaySegment {
  request : RewriteRequest
  before_concl : @kernel.Term
  after_concl : @kernel.Term
  steps : Array[ReplayStepKind]
}

pub struct ReplayObligation {
  before_concl : @kernel.Term
  after_concl : @kernel.Term
  segments : Array[ReplaySegment]
}

pub fn research_replay_segment(RewriteRequest, @kernel.Term, @kernel.Term, Array[ReplayStepKind]) -> ReplaySegment
pub fn research_replay_obligation(@kernel.Term, @kernel.Term, Array[ReplaySegment]) -> ReplayObligation
```

### `research_validate_replay_obligation`

`research_validate_replay_obligation(state, prelude, locals, obligation)` checks an obligation by rebuilding every segment from its request with kernel rules and comparing the result, the steps and the chaining with what the obligation records.

```mbti
pub fn research_validate_replay_obligation(@kernel.KernelState, @logic.PropPrelude, Array[(String, @kernel.Term)], ReplayObligation) -> Result[Unit, @kernel.LogicError]
```

A hand-made or stale obligation fails with a `LogicError`.

```moonbit
test "rewrite" {
  let st = @logic.install_prop_prelude(@kernel.empty_kernel_state()).unwrap()
  let pre = @logic.default_prop_prelude()
  let bool = @kernel.bool_ty()
  let p = @kernel.mk_var("p", bool)
  let q = @kernel.mk_var("q", bool)
  let f = @kernel.mk_var("f", @kernel.fun_ty(bool, bool))
  let locals = [("h", @kernel.mk_eq(p, q).unwrap())]
  // rewrite the argument of f p with h : p = q
  let req = @research_rewrite.research_rewrite_request(
    @research_rewrite.research_local_equality("h"),
    @research_rewrite.research_left_to_right(),
    [@research_rewrite.research_site_comb_arg()],
  )
  guard @research_rewrite.research_rewrite_term_concl(st, pre, locals, @kernel.mk_comb(f, p), req)
    is Rewritten(after, obligation) else {
    fail("expected a rewrite")
  }
  inspect(@kernel.term_to_string(after), content="Comb(Var(f : fun(bool, bool)), Var(q : bool))")
  let steps = obligation.segments[0].steps.map(@research_rewrite.research_step_name)
  inspect(steps.join(", "), content="ResolveWitness, Congruence")
  inspect(@research_rewrite.research_validate_replay_obligation(st, pre, locals, obligation) is Ok(_), content="true")
  // without the hypothesis h the obligation does not replay
  inspect(@research_rewrite.research_validate_replay_obligation(st, pre, [], obligation) is Err(_), content="true")
}
```
