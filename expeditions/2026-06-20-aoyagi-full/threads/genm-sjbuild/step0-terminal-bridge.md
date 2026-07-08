# STEP-0 VERIFY-FIRST GATE — the terminal count↔monomial bridge

**Thread:** `genm-sjbuild` (formaliser, R1-UPPER CoV mountain → `sjJointResolution`).
**Base:** `expedition/aoyagi-full` @ `d9b8a7ea`. **No Lean build in STEP 0** — exact `ℕ`-recursion
enumeration (`step0_recurse.py`, `step0_sweep.py`) + a decorrelated `local-codex-consult` (xhigh, my
model+verdict withheld: `codex/step0-{prompt,answer}.md`).

## THE QUESTION (the sharp risk r1predicate/Codex flagged)

Is `½·minAdm(remChain π) ≤ monomialThreshold d (sharedDivisorExp) jac` **UNIFORM over ALL route
terminals** (all Case-1/Case-2 chart sequences)? Checked exactly on `(3,3,4)`, `(2,2,2,2)`, `(3,3,3,4)`.
If NOT uniform → the decoration must enter the threshold (a re-scope).

## VERDICT — GATE PASS

**On the three named anchors the bridge is uniform — VACUOUSLY, because the monomial terminal
`sjLoss_terminal` is NEVER reached.** Every chart the recursion visits on these three chains is closed
by regime A (full-rank exponent shift) + regime B (Morse dominance) + the free-matrix base, at threshold
**exactly `½·minAdm`** (the soundness gate `minAdm ≤ peelCharge + minAdm(redChain)` makes the shift land).
The decorated recursion may still be BUILT with the monomial terminal (the pinned design), but the bridge
statement it discharges cannot fall below `½·minAdm` on any terminal these anchors reach.

**Decorrelated Codex (xhigh, model+verdict withheld) reached the SAME finding independently** — derived the
load-bearing condition from scratch (identical to mine), confirmed no load-bearing chart on the three
anchors, and confirmed the bridge holds on a genuine load-bearing chart. Two decorrelated analyses
converged.

**PROCEED to the multi-tide build.** No re-scope; the decoration does NOT need to enter the threshold.

## The model (the three regimes + the two terminals)

At a chain `N = M_cur` the recursion reaches (local threshold `c' < ½·minAdm(N)`), peel cut `t ≥ 1`,
corank block `Γ` of shape `p×q` (`p = N₀−t`, `q = N₁−t`, charge `pq`). `Γ` couples to the deeper factor
`Q_b` (the `q` non-pivot node-1 rows pushed through the deeper product of widths `N₂..N_L`), whose generic
rank is `r = min(q, τ)`, `τ = min(N₂,…,N_L)`. The banked bricks (`RouteMSJCorankPure`):

- **regime A** (`matBox_corank_residual_absZ_le`, `c' > pq/2`, `W>0` strict, `Q_b` FULL ROW RANK `r=q`):
  shift `c' ↦ c'−pq/2`, hand `∫ (W z)^{−(c'−pq/2)}` to the IH (box-finiteness of the strictly-shorter
  `redChain t N`). Soundness gate lands it below `½·minAdm(redChain t N)`.
- **regime B** (`matBox_corank_dominates_absZ_lt_top`, `c' < p·r/2`, `W ≥ 0` any): the block
  Morse-dominates (**effective Morse dimension `= p·r`**, the linear rank of `Γ ↦ Γ·Q_b`; the `p·(q−r)`
  kernel directions are FLAT and give a bounded box constant). Finite directly.
- **free-matrix base** (`sjBase1_freeMatrix`, 2-node leaf): EXACT `½·M₀M₁ = ½·minAdm`.
- **monomial terminal** (`sjLoss_terminal_lintegral_lt_top`): the toric/normal-crossing endpoint. Genuinely
  load-bearing ONLY where NEITHER regime covers some admissible `c'`.

## The load-bearing condition (derived, decorrelated-confirmed)

The monomial terminal is genuinely load-bearing at `(N, t)` iff (Codex Q2, identical to my derivation)

    p > 0,   r < q  (rank-deficient Q_b),   and   p·r < minAdm(N).

Equivalently `t < N₀`, `N₁−t > τ`, and `(N₀−t)·τ < minAdm(N)`. Reason: if `r = q`, regime A (above
`pq/2`) and regime B (below `pq/2`) tile all `c'`. If `r < q`, regime A is unavailable, and regime B leaves
the open gap `c' ∈ (p·r/2, ½·minAdm(N))` exactly when `p·r < minAdm(N)`.

## The exact enumeration (`step0_recurse.py`, `step0_sweep.py`)

Full recursive enumeration of every `(chain, cut)` the recursion visits:

| anchor | minAdm | charts visited | rank-deficient charts | **load-bearing monomial charts** |
|---|---|---|---|---|
| `(3,3,4)`     | 8 | 3 | 0 | **0** |
| `(2,2,2,2)`   | 3 | 5 | 0 | **0** |
| `(3,3,3,4)`   | 7 | 9 | 0 | **0** |
| `(3,3,2,2)`   | 4 | 8 | 0 | **0** |
| `(4,4,2,2)`   | 4 | 11 | 1 (`t=1`, `3×3`, charge 9) | **0** (regime B: `p·r=6 ≥ 4=minAdm`) |

For the three NAMED anchors: every chart has `q = N₁−t ≤ τ` (or `p = 0`), so `r = q` (full-rank `Q_b`) —
regimes A/B tile every `c'`, no monomial terminal reached. Codex verified this per chart independently
(Q3). `(4,4,2,2)` has a rank-deficient chart but regime B still covers it (`p·r = 6 ≥ minAdm = 4`).

## The genuine load-bearing case IS uniform too (spot-check `(3,4,2)`)

Load-bearing charts DO exist for general chains (5990 in the arity-3/4/5, widths-1..6 sweep) — e.g.
`(3,4,2)` at `t=1`: `p=2, q=3, r=min(3,2)=2, p·r=4 < 6 = minAdm`, so `c' ∈ (2,3)` is uncovered by
regimes A/B. There the bridge STILL holds (Codex Q4, decorrelated): on the `rank(Q_b)=2` chart the loss is
the JOINT block `‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`; the pivot-coupled `Q̃_p` contributes `t·M_last = 1·2 = 2`
dimensions and the block image `Γ·Q_b` contributes `p·r = 4`, for total Morse dimension `2 + 4 = 6 =
minAdm(3,4,2)` — threshold `3 = ½·minAdm`. So the count↔monomial threshold `= ½·minAdm` on this leaf too.
The general uniformity is banked at the model level by `routeLayerAtlas_value`
(`⨅ over route leaves monomialThreshold = ½·minAdm`, sorry-free, UNCONDITIONAL) ⟹ every leaf's threshold
`≥ ½·minAdm`.

## Load-bearing caveats carried into the build (NOT hand-waves)

1. **`c' = pq/2` boundary** (r1predicate/Codex GAP): the two regime lemmas cover `c' < p·r/2` and
   `c' > pq/2` (with `r=q`); the point `c' = pq/2` is covered by NEITHER. Needs an explicit ε-approach in
   `decorated_peel_step` (`c' < c'' < min(carrierThreshold, next regime)`, regime A at `c''`). Named
   obligation. Bites where `pq` even and `pq/2 < ½·minAdm` (e.g. `(3,3,4)` `c'=2`, `pq=4`).
2. **Actual vs generic rank on the chart** (Codex Q1 caveat): regime B's effective dim `p·r` uses the
   rank on the chart/stratum; a measure-zero sub-locus where `Q_b` drops further must be handled by
   descent, not assumed away. Standard stratification; the pivot-chart cover `pivotChartCover_matBox_le_sum`
   (banked, exhaustive over a field) supplies it.
3. **No circular citation** (Codex Q4): the bridge `monomialThreshold(terminal) ≥ ½·minAdm` must be proved
   from the terminal exponents `(sharedDivisorExp, jac)` — NOT by citing Aoyagi's `rlct = C/2` (that is the
   payoff the build feeds, so using it here is circular). `routeLayerAtlas_value` supplies the S2-free
   combinatorial fold at the single-divisor model; piece 6 (`decorated_base`) must map the decorated
   terminal's `(d, k, h)` onto (or dominate) that model.

## Scope note for the controller (the finding, plainly)

The three named STEP-0 anchors are ALL regime-A/B clean — they do NOT exercise the monomial terminal.
So STEP 0's literal check is a **vacuous PASS** on them (uniform because no monomial terminal is reached).
The genuine monomial-terminal bridge is load-bearing only on rank-deficient chains with a small deeper
width (e.g. `(3,4,2)`, `(3,3,1)`), verified uniform on a spot-check + banked at the model level by
`routeLayerAtlas_value`. Two consequences:
- The predicate/decoration/peel-step build (pieces 1–5, 7) is numerically independent of the bridge value
  and proceeds unblocked.
- `decorated_base` (piece 6) carries the real bridge obligation, discharged against `routeLayerAtlas_value`,
  not against a numeric non-uniformity (there is none).

## DATA index (exact)
- `step0_bridge.py` — per-stratum layer trace (regime classification, terminal chain, charges = minAdm).
- `step0_recurse.py` — full recursive chart enumeration; rank-deficiency flag per `(chain, cut)`.
- `step0_sweep.py` — the load-bearing condition swept over arity 3/4/5, widths 1..6; named-anchor + witness
  confirmation (all 0).
- `codex/step0-{prompt,answer}.md` — decorrelated consult (model+verdict withheld; independent convergence
  on the load-bearing condition, the named-anchor verdict, and the `(3,4,2)` bridge).
