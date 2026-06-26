**1. SCOPING VERDICT**

1. **C: package a concrete `(2,2,2)` `IsRouteMCover` first, without general `routeStep`.** Highest EV/risk. Use existing fixed-box finiteness and divergence facts to satisfy the bridge fields, with a concrete leaf family whose `iInf` is `3/2`.
   Biggest risk: the bridge consumer may insist on literal `routeMIota H222`; then you must align with `routeAtlas`, not just an explicit `ι`.

2. **B: concrete `(2,2,2)` route/cover anchor.** Good if literal `routeMIota H222` is mandatory.
   Biggest risk: a total global `routeStep` for only one case tempts an arbitrary fallback, reintroducing the vacuity trap.

3. **A: fully general `routeStep` + general `cover_le`.** Lowest EV/risk right now.
   Biggest risk: two missing constructions interact: no Lean `schurState/residualCore`, and no general WellFounded lintegral recursion.

Verified: `RouteStep.branch` is raw `split/codim/witness`, and `routeAtlas` ignores `witness` while recursing on `split.red` in [RouteMRecursion.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:150). Inference: the cheapest milestone is bridge packaging, not rebuilding the general resolution.

**2. THE routeStep DECOUPLING**

**No.** It is logically harmless only as raw data, but unsound as a claimed resolution object: the recursive child exponents would describe `dlnLoss split.red 0`, while the actual pullback residual is whatever the pivot geometry produces.

Minimal honest general `routeStep`: either define `schurState` in Lean and set/prove `split.red = schurState`, or add a `ValidRouteStep M step`/certified branch field proving the per-cell pullback residual transports or squeezes to `dlnLoss (split c).red 0`. The `PivotWitness` certifies codim/value combinatorics; it does not certify analytic descent.

**3. cover_le REACHABILITY for `(2,2,2)`**

Reachable, but do **not** derive it from `rlctAtOn myF222 0 = 3/2` alone. Equality gives a threshold value, not the stated quantitative inequality, not fixed-`U` finiteness, and not endpoint divergence.

Slicker route for `cover_le`: use existing fixed-box finiteness `myF222_threshold_lt_top'` over `openBox` for `c' < 3/2`, plus positivity/finite-ness of the chosen monomial RHS, and choose a finite scalar `C` abstractly. For `c' ≥ 3/2`, prove the RHS monomial integral is `⊤`, so the inequality is trivial with `C = 1`.

So: `cover_le` as a field requires the inequality, but it does **not** genuinely require reconstructing the explicit 24-leaf Σ change-of-variables if the bridge only uses it for finiteness. A weaker single-integral finiteness theorem plus a positive monomial RHS can manufacture the inequality.

Verified: fixed-box finiteness exists as `myF222_threshold_lt_top'` in [Case222CoverGETail.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1168). The abstract `IsRouteMCover` name was not visible in this worktree, so I am relying on your pasted signature there.

**4. ORDER**

1. Prove a tiny ENNReal scaling lemma:
   finite `A`, positive finite `B` implies `∃ C < ⊤, A ≤ C * B`; plus the `B = ⊤` case.
   Check: `cover_le` below threshold reduces to this lemma, not to chart algebra.

2. For one concrete `(2,2,2)` leaf datum, preferably the existing unit datum with threshold `3/2`, prove RHS facts:
   finite and positive for `c' < 3/2`, infinite for `3/2 ≤ c'`.
   Check: the `c' = 0` and `c' = 3/2` boundary cases compile.

3. Assemble `IsRouteMCover myF222 openBox Unit d k h`, then transport to `dlnLoss H222 0` only if required.
   Check: `cover_ge_div` works at endpoint `c' = 3/2`; strict `>` is not enough for the pasted bridge.