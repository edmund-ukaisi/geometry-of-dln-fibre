# Statement card — A1 band discharge (forward-max witness)

Thread: `band-discharge` (achiever "band" — the last A1 seam of `lambdaCore_eq_clean`).
Worktree branch `worktree-agent-add28546023f3083e` (rebased onto the `rung0-defs` green base).
SHA: pending controller integration (uncommitted on the worktree).

## What this tide delivered (all GREEN)

The achiever band — the `hband` input to `QFeas_qStar` inside `lambdaCore_eq_clean` — is no longer an
in-proof `sorry`. It is now **fully proven from a single isolated lemma** `forwardMax_prefix_band`,
with the entire witness construction and the prefix↔suffix glue green.

> **Claim (band).** For each `j : Fin L`, `S'_{j+2} − admBound_j ≤ prefix_{j+1}(qStar)`
> (`S'_n = ∑_{i<n} M⁽ⁱ⁾`, `qStar = backwardGreedy (Mwidths M) (Ymulti M)`).
>
> - **Lean:** the `hband` block inside `DLNFibre.DLN.RLCT.lambdaCore_eq_clean`
>   (`lean/DLNFibre/DLN/RLCT/Skeleton.lean`).
> - **Gloss.** The achiever ordering's prefix sums clear the admissibility floor — the corridor
>   condition `QFeas_qStar` needs.
> - **Proved (this tide, green):**
>   - `forwardMax` / `forwardHead` / `liveCand` — the front-greedy realizer, defined proof-free
>     (total, `0` fallback) with `open Classical` for the `Dom`-decidable filter (the friction the
>     brief flagged as the known wall — solved, green).
>   - `feasiblePerm_dom` — a feasible perm of `R` certifies `Dom b R` (count argument).
>   - `liveCand_nonempty` — `backwardGreedy`'s head is a live candidate (feasible + keeps `Dom`).
>   - `forwardHead_ge` / `_mem` / `_dom` / `live_le_forwardHead` — head specs under `Dom`.
>   - `forwardMax_perm` / `forwardMax_feasible` — the realizer is a feasible perm of the pool.
>   - The **glue**: `prefix(qStar) ≥ prefix(forwardMax)` via `backwardGreedy_suffix_le` + equal
>     totals; the `admBound`-cases conversion (`j=0`: `min(M⁰,M¹)`; `j≥1`: `M⁽ʲ⁺¹⁾`); the
>     `sum_range_getD_eq_take` prefix-as-take-sum bridge. All green.
> - **Deferred (the one open seam):** `forwardMax_prefix_band` — `prefix_k(forwardMax) ≥ S'_k`
>   (`k≥2`) / `≥ max(M⁰,M¹)` (`k=1`). Numerically 0-fail (19525 cases). The arithmetic heart;
>   reduces to `good_floor_core` via the **window lemma** (see below). A single `sorry`.
> - **Cited.** none.
> - **Status.** band-glue sorry-free; `forwardMax_prefix_band` open (documented). Build:
>   `lake build DLNFibre.DLN.RLCT.Skeleton` GREEN (2669 jobs).

## The remaining seam, precisely (verified proof plan)

`forwardMax_prefix_band` is **not abstract in `Dom`** (the bound
`prefix_k ≥ (∑R−∑b) + ∑_{i<k}b[i]` FAILS for generic `Dom(b,R)`, 20000 cases) — it needs the
achiever structure of `Yvec` via `good_floor_core`. Verified-dead fixed-permutation witnesses:
rank-match / anti-rank / top-largest-block / smallest-`k`-sum (the brief's "4705": min feasible
suffix `> smallestK(Yvec, L−k)` in 4705 cases — feasibility forces larger tail values). The
forward-max (max-feasible-prefix) is the unique witness.

**Cleanest route (suffix form).** Equivalently prove `suffix_k(qStar) ≤ tailM_k = ∑_{i=k}^L M⁽ⁱ⁾`
on `qStar` by backward induction maintaining `I2 : suffix_{j+1} ≤ tailM_{j+1}`. The step is the
**window lemma** (verified 0-fail, 19525 cases): at greedy step `j` (width `M⁽ʲ⁺¹⁾`) the live pool
holds a value `y` with `M⁽ʲ⁺¹⁾ ≤ y ≤ tailM_j − suffix_{j+1}`; minimality of the greedy pick gives
`vⱼ ≤ y`, propagating `I2`. Window existence is where `good_floor_core` enters. Est. ~150 lines
(pool-state tracking through the `backwardGreedy` recursion + the window arithmetic).

**Alt route (forward).** Prove `forwardMax` maximises every prefix (mirror of
`BGEngine.backwardGreedy_suffix_le`, ~130 lines), then bound its prefix by the same window lemma.
