# Statement cards — T3 coverage (coverage-t07)

## Rung 1 — the per-blow-up LOCAL COVERING LEMMA (corank ≥ 2)

> **Claim.** For the blow-up of `ℝ^d` (`d ≥ 1`) at the coordinate origin, the `d` standard affine
> "pivot" charts in the max-modulus normalization, restricted to their bounded domains, have images
> whose union is EXACTLY the cube `[−R,R]^d` (`R ≥ 0`). The `⊇` (covering) half is the load-bearing
> content — it is Aoyagi's implicit "the charts cover by a blow-up process" made a theorem — and it
> requires the FULL residual-`d` family: a single fixed "corner" chart misses `{x : x_corner = 0,
> x ≠ 0}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Engine.iUnion_pivotChart_image_eq_cubeBox`
>   (+ `cubeBox_subset_iUnion_pivotChart_image` = the isolated `⊇` half;
>   `corner_chart_not_cover` = the corner-gap ¬-theorem)
>   (`lean/DLNFibre/DLN/RLCT/Engine/PivotCover.lean` @ `f17b2c215`)
> - **Gloss.** `pivotChart i u = fun k => if k = i then u i else u i * u k` (the `i`-th affine
>   blow-up chart; exceptional divisor `{u i = 0}`, Jacobian `|det| = |u i|^{d−1}`).
>   `pivotChartDom i R = { u | |u i| ≤ R ∧ ∀ k ≠ i, |u k| ≤ 1 }` (bounded: pivot in `[−R,R]`, ratios
>   in `[−1,1]`). The theorem: `⋃ i : Fin d, pivotChart i '' pivotChartDom i R = cubeBox d R` under
>   `0 < d` and `0 ≤ R`. `⊇`: every cube point is reached by the chart of its max-modulus coordinate;
>   `⊆`: each chart image stays in the cube. `corner_chart_not_cover`: `(0,ε)` (`ε > 0`) is NOT in
>   the image of the pivot-`0` chart on ANY domain (`Set.univ`).
> - **Proved.** The set equality (both inclusions), unconditional over `ℝ`, all `d ≥ 1`, all `R ≥ 0`;
>   the corner-gap ¬-theorem at `d = 2`. Axioms `[propext, Classical.choice, Quot.sound]`
>   (`#print axioms`, forced elaboration — no `sorryAx`, no `native_decide`).
> - **Assumed.** `0 < d` (a nonempty coordinate block — else there is no pivot) and `0 ≤ R`
>   (nonnegative box radius). Both are genuine hypotheses of the claim, not laundering.
> - **Cited.** none — elementary; the only Mathlib input is `Finset.exists_max_image` (argmax of a
>   finite family). NOT dependent on `rlct = c*`, `cited_aoyagi_dln`, `RlctInterface`, or region-glue
>   (circularity guard clear — the module imports only `Foundations.S1Cover` for `cubeBox`).
> - **Deferred.** THE FOLD. This is the single-blow-up ATOM; the name denotes only the pivot cover of
>   ONE origin blow-up of `ℝ^d`. Embedding it into `ChartBridge`'s flat-coordinate tree-level
>   image-cover (`EngineDefs.lean:76` — over `Fin (flatDim M)`, per-case Case-1/Case-2 centers, the
>   `chartMap` = root→leaf edge-substitution fold) is rung 2, NOT done here. The per-leaf a.e.-`InjOn`
>   (image-cover lane) and the construction-owned `LeafPullback`/`LeafJacobian` proofs over the built
>   atlas are rungs 2–3.
> - **Structure & ideas observed.** N/A — new-claim theorem, not a pen-and-paper handoff. The
>   generative observation for the fold: the tree-level cover is a tree induction whose per-node atom
>   is exactly this lemma; the max-modulus normalization gives bounded ratio domains for free (serving
>   `ChartBridge`'s bounded-`srcBox` requirement), and `range(pivotChart i | dom) = {x : x_i is a
>   max-modulus coord}`, so the cover reduces to "every tuple has an argmax of `|·|`."
> - **Route.** `⊇` = argmax of `|·|` (`Finset.exists_max_image` on `univ`) + explicit preimage
>   `u = Function.update (·/x i) i (x i)` (pivot = `x i`, ratios = `x k / x i`, bounded by the
>   argmax); the `x i = 0` degenerate case takes `u = 0`. `⊆` = `|u i · u k| ≤ R·1`.
> - **Numerical witness.** `threads/10-coverage/battery/c-pivot-chart-cover.py` (exit-0, exact
>   rational): COVER (exhaustive grid `d = 1..4`), BOUND, GAP (reproduces `cert-atlas-probe`
>   Verdict 1(b)'s `(0,ε)` miss), JAC (`|det D(pivotChart i)| = |u i|^{d−1}`, symbolic).
> - **Status.** sorry-free (fidelity read PENDING — the fork-12 commissioning gate: does the atom
>   faithfully render "cover by a blow-up process"? routed to elder/reviewer via the controller).
