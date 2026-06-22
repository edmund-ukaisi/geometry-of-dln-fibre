# (S) surjectivity — WITNESS proof sketch (paths ↠ Adm M), carried on RankPattern/Gabriel (pp-hall, 2026-06-22, #134)

**The witness leg on the single R1.6 residual.** #133 reduced R1.6 to four conjuncts of
`IsResolutionAtlas`; three (A,K,C) are certified/structural, and **(S) `stratum_surjective`** —
every admissible stratum `T ∈ Adm M` is reached by some pivot-tree root-to-leaf path — is the residual.
This is the math PROOF SKETCH that (S) HOLDS (the witness direction), carried on `Core.RankPattern` /
`Core.OrbitKostant` (Gabriel), as design input for the (S) formaliser (cover task #21). Decorrelated from
pp3's obstruction leg (its "missed branch" hunt is the same question from the no-go side — wall held).

## VERDICT: (S) HOLDS. Every admissible stratum is reached; no missed branch.

The argument is a three-step reduction to facts the `Core` engine already carries: (1) `Adm M` = the
admissible **prefix-rank** cone; (2) every admissible prefix-rank tuple is **realizable** (a tuple has
exactly those partial ranks) — the staircase / Gabriel normal form; (3) the recursion's per-level
pivot/minor choice **is** the resolved rank, so each realizable stratum is the binding center of some path.

## Step 1 — `Adm M` IS the admissible prefix-rank cone (the index identification)
The prefix-rank tuple of a tuple `C = (C_1,…,C_L)` is `t_j := rank(C_1 ⋯ C_j)` (`j = 1..L`; `t_L = 0` at
the deepest core point). Its constraints are exactly `admPred` (`Foundations/Lambda.lean:51`):
- **weak-decrease** `t_j ≤ t_{j-1}`: `rank(P·C_{j}) ≤ rank(P)` (a longer product can't raise rank) — the
  `admPred` monotone clause `∀ i ≤ j, T j ≤ T i`;
- **block bound** `t_j ≤ M_{j+1}` (columns) and `t_1 ≤ min(M_0,M_1)` (rows ∧ cols) — `admBound`;
- **deepest** `t_L = 0` (product vanishes) — `admPred`'s last clause.
So `Adm M` = `{prefix-rank tuples of tuples in {∏C=0}}` *as a constraint set*. The codim is
`Mval M T = codim S(T)` (thread-03, proven general-L; `g134_realizable_eq_adm.py` cross-checks the cone).

## Step 2 — every admissible `T ∈ Adm M` is REALIZABLE (the stratum is nonempty)
A surjectivity claim onto `Adm M` is only well-posed if each admissible `T` actually has a stratum point.
It does: build the **staircase normal form** — `C_s` = the rank-`(needed)` partial-identity block so the
cumulative product ranks hit `T` exactly. Verified to realize EVERY admissible `T` exactly on `(2,2,2)`
(3 strata), `(3,3,3)` (4), `(2,2,2,2)` (6) (`g134_realizable_eq_adm.py`: all partial ranks match `T`).
This is the **Gabriel normal form** `⊕ M^{m̄}` in the Core engine: `Orbit.baseChange_normalForm` realizes
each rank pattern, and `RealizableRank d = Set.range (rankFn d)` (`OrbitKostant.lean:97`) is by
construction the set of patterns hit by a tuple. The admissible prefix tuples `T` are the **prefix
projection** `r_{1,j}` of a realizable full rank pattern `r_{a,b}` — so `Adm M ↪ {prefix(realizable)}`,
and Step-2's staircase exhibits the realizing tuple. [Worked: `(2,2,2)` t=(0,0),(1,0),(2,0) each realized
by an explicit `(A1,A2)` with `rank A1 = t_1`, `A1·A2 = 0`, `g134_surjectivity_sketch.py`.]

## Step 3 — the recursion REACHES each realizable stratum (the pivot-choice = resolved-rank)
The pivot tree branches at each level on **which minor is the nonzero pivot** of the active factor — i.e.
on the **resolved rank** of that factor. A root-to-leaf path is a sequence of per-level resolved ranks;
its binding (min-codim) center is the stratum `S(t)` with those partial ranks. Concretely (the witness
path for a given `T`): blow up `C_1`'s rank-defect to expose rank `t_1` (pivot on a `t_1×t_1` minor); the
Schur step (#127/#129) resolves the `(M_1 − t_1)` pivot units into regular squares; descend to the reduced
node on `‖S·A2red‖²` (a rank-`t_1` chain) whose deeper partial ranks `t_2 ≥ t_3 ≥ …` are reached by the
SAME mechanism on the reduced factors. The binding center of this path is exactly `S(T)`, codim
`Mval M T` (#133 fact C). So **for every admissible `T`, the path choosing resolved ranks `= T` at each
level binds `S(T)`** — `path-image ⊇ Adm M`. Surjectivity holds. [`g134_surjectivity_sketch.py`: each
`(2,2,2)` stratum reached; the `(3,3,3)` cone realized by `A_s` rank-`t_s` staircase.]

## The carrier: `Core.RankPattern` / `OrbitKostant` (Gabriel) — confirmed
The proof's load-bearing facts live in the abstract Core engine (network-free, the quiver-orbit ↔
rank-pattern translation the controller named):
- `rankFn d A` — the complete rank-pattern invariant; `rankFn_eq_iff_orbit` (orbits ↔ patterns).
- `RealizableRank d = Set.range (rankFn d)` — every realizable pattern is hit (Step 2's "nonempty
  stratum" = a point of this range).
- `RankPattern.cumulDiffEquiv` — Prop 3.1 (cumul ↔ diff): the rank pattern `r_{ab}` ↔ its Gabriel
  bar-multiplicities `m̄` (`Orbit.exists_cumul_barMult`); the realizing tuple is `⊕ M^{m̄}`
  (`Orbit.baseChange_normalForm`).
- `RankLocusClosed` — `S(t)⁻` is the determinantal rank locus (closed); the strata partition `{∏C=0}`.

**The bridge for the formaliser:** (S) `∀ T ∈ Adm M, ∃ path, stratum(path) = T` reduces to
`∀ T ∈ Adm M, T ∈ prefix(RealizableRank M)` (Step 2, via `baseChange_normalForm`) **+** the recursion's
`stratum`-tagging being the prefix-rank readout (Step 3, the pivot-choice = resolved-rank, structural in
the chart construction the cover #21 builds). Step 2 is pure Core (Gabriel realizability); Step 3 ties the
DLN chart construction's branch tag to the Core rank pattern. The DLN↔Core seam is `prefix : RealizableRank
M → Adm M` (the first-row projection `r_{1,j}` of a realizable pattern is an admissible prefix tuple).

## Commit on `threshold_eq` (the #133 open choice)
I commit to the **`≥ + one achiever`** form, NOT the per-path equality. Reason: the per-path equality
`monomialThreshold_i = ½·Mval(stratum i)` requires `stratum i` to be the path's binding (min-codim)
center, which is fiddly to define cleanly (a path may cross several exceptional divisors; the binding one
is the argmin). The laxer pair closes `resolution_value_of_atlas` just as cleanly and is robust to the
`stratum`-definition:
- **(C≥)** `∀ i, ½·(min_t Mval M T) ≤ monomialThreshold (d i)(k i)(h i)` — every path's threshold is at
  least the codim-min (the **no-undershoot** lower bound, from `mult_one` K + every center admissible A:
  each divisor ratio `= codim/2 ≥ ½·min_t Mval`). This is `monomialThreshold_ge_of_mult` (green,
  `Skeleton.lean:134`) applied per chart with `m = min_t Mval`.
- **(C=∃)** `∃ i, monomialThreshold (d i)(k i)(h i) = ½·(min_t Mval M T)` — one path (through the
  minimising stratum's binding divisor) achieves it (the **no-over-estimate** upper bound; this is where
  (S) surjectivity bites — surjectivity guarantees the min stratum IS reached by some path). This is
  `monomialThreshold_le_regularSeq` (green, `Skeleton.lean:149`) on that path's binding divisor.

Then `⨅_i monomialThreshold = ½·min_t Mval = ofReal(lambdaCore M)` by `le_antisymm`: `(C≥)` gives
`⨅ ≥ ½·min` (`le_iInf`), `(C=∃)` gives `⨅ ≤ ½·min` (`iInf_le` at the achiever). This is cleaner than the
per-path equality + the `min-over-image = min-over-Adm` rearrangement, AND it isolates surjectivity to
exactly the `(C=∃)` achiever (the minimising stratum reached). **Revised obligation for #133/#21:** replace
`threshold_eq` (the per-path equality) by `(C≥)` + `(C=∃)`; drop `stratum`-as-binding-center (no longer
needed — `(C=∃)` only needs ONE achieving path, and `(C≥)` is uniform via `monomialThreshold_ge_of_mult`).
`stratum_surjective` (S) is then used ONLY to produce the `(C=∃)` achiever (the path reaching the
minimiser), which is a WEAKER use of (S) than "every stratum reached" — **`(C=∃)` needs only that the
MINIMISING stratum is reached, not all of `Adm M`.**

### Sharpened (S) — only the MINIMISER need be reached
This is the witness leg's sharpest contribution: for the VALUE `⨅ = ½·min_t Mval`, surjectivity onto all
of `Adm M` is MORE than needed. The assembly needs only:
- **(S-min)** the minimising stratum `T* ∈ argmin Mval` is reached by some path (for `(C=∃)`), and
- **(A+K)** every center is admissible with `k_E=1` (for `(C≥)`, uniform — no per-stratum reaching).

So the residual shrinks: prove **one** path reaches a minimiser (`S-min`), not the full surjection. The
minimiser is the **top-dimensional stratum** (largest `S(t)`, smallest codim = `min_t Mval`); a path
reaching it is the binding-divisor branch of #132/r1-design §2 ((2,2,2): the `ρ`-chart resolving the
codim-3 incidence stratum, ratio 3/2). This is a single explicit branch, far cheaper than the full
combinatorial surjection. **Recommendation: state the obligation as `(C≥)` [uniform, green via
`monomialThreshold_ge_of_mult`] + `(S-min)` [one path reaches a minimiser] + the achiever's
`monomialThreshold_le_regularSeq`.** Full surjectivity is the clean conceptual statement; `(S-min)` is the
minimal load-bearing core.

## Most likely thing to break this
`(S-min)` rests on the minimising stratum being reachable by a pivot path. The risk: that the path to the
minimiser is non-trivial. Check: is `argmin Mval` the generic stratum? On `(2,2,2)`, `argmin = t=(1,0)`
(rank-1, codim 3) — **NOT** the generic `t=(2,0)` (rank-2, codim 4)! So the minimiser is the rank-1
incidence stratum, reached at the SECOND level (after the `C_1`-blow-up, the residual's rank-drop), not by
the trivial first chart. So `(S-min)` genuinely needs the recursion to reach a deeper minimiser — this is
the real (modest) content of `(S-min)`: one explicit path (the binding branch of r1-design §2), but not the
trivial first chart. [`g134` confirms argmin is the rank-1 stratum for (2,2,2)/(3,3,3).]

## Net for the formaliser (#21 cover + the (S) prover)
- **Restate the value-consequence** via `(C≥)` + `(C=∃)` + `le_antisymm` (cleaner than per-path equality);
  this drops the `stratum`-as-binding-center fiddliness and uses green `monomialThreshold_ge_of_mult` /
  `monomialThreshold_le_regularSeq`.
- **The residual shrinks** to `(S-min)`: ONE path reaches a minimising stratum (the binding branch). Full
  `stratum_surjective` is the conceptual statement; `(S-min)` is the load-bearing minimum.
- **Carrier:** `(S-min)`'s realizability = `Core.OrbitKostant` (`baseChange_normalForm`, the minimiser is
  realizable); the path-reaches-it = the DLN chart construction's binding branch (#132 §2). The seam is
  `prefix : RealizableRank M → Adm M`.

Decorrelation: pp-hall exact (2 scripts `g134_*` in `g129-scripts/`: surjectivity witness on (2,2,2),
realizability of every admissible tuple on (2,2,2)/(3,3,3)/(2,2,2,2)) + the Core-engine fact survey
(`rankFn`/`RealizableRank`/`baseChange_normalForm`/`cumulDiffEquiv`). Codex leg on the math (route + 5
hinges, including this surjectivity question's "no missed branch") already ran #132 — converged. A fresh
Codex pass on the `(S-min)` sharpening is optional belt-and-suspenders. Builds on #133 (the obligation),
#132 (the 5 hinges), #131 (ideal-membership/codim), r1-design §1-2 (strata + binding divisor),
`Core.OrbitKostant`/`RankPattern` (the realizability carrier). Wall held: have not read pp3's #17.
