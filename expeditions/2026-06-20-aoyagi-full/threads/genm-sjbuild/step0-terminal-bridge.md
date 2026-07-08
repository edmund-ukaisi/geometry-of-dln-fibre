# STEP-0 VERIFY-FIRST GATE — the terminal count↔monomial bridge

**Thread:** `genm-sjbuild` (formaliser, R1-UPPER CoV mountain → `sjJointResolution`).
**Base:** `expedition/aoyagi-full` @ `d9b8a7ea`. **No Lean build in STEP 0** — exact `ℕ`-recursion
enumeration (`step0_recurse.py`, `step0_sweep.py`) + a decorrelated `local-codex-consult` (xhigh, my
model+verdict withheld: `codex/step0-{prompt,answer}.md`).

## THE QUESTION (the sharp risk r1predicate/Codex flagged)

Is `½·minAdm(remChain π) ≤ monomialThreshold d (sharedDivisorExp) jac` **UNIFORM over ALL route
terminals** (all Case-1/Case-2 chart sequences)? Checked exactly on `(3,3,4)`, `(2,2,2,2)`, `(3,3,3,4)`.
If NOT uniform → the decoration must enter the threshold (a re-scope).

## VERDICT — GATE PASS for the NARROW decision (the decoration does NOT enter the threshold)

The pinned cert's sharp question was: does the carrier threshold need to become
`½·min(minAdm(remChain), <a decoration-dependent quantity>)`, i.e. must the decoration enter the threshold?
**Answer: no.** `carrierThreshold N = ½·minAdm N` (decoration-free) is sound, on two grounds:

1. **The three named anchors never reach the monomial terminal.** Every chart the recursion visits on
   `(3,3,4)`, `(2,2,2,2)`, `(3,3,3,4)` is closed by regime A (full-rank exponent shift) + regime B (Morse
   dominance) + the free-matrix base, at threshold **exactly `½·minAdm`** (the soundness gate
   `minAdm ≤ peelCharge + minAdm(redChain)` makes the shift land). So on the NAMED anchors the bridge holds
   **vacuously** — a vacuous test of the sharp risk, which is why the load-bearing case below matters.
2. **On the load-bearing charts (where the monomial terminal IS reached), the bridge is an INEQUALITY
   `½·minAdm ≤ threshold` with no counterexample** across 23358 sweep charts (`step0_ineq.py`). The
   decoration does not lower the threshold below `½·minAdm`.

**Decorrelated Codex (xhigh, model+verdict withheld) reached the SAME model + load-bearing condition
independently**, and confirmed no load-bearing chart on the three anchors. On the general uniformity it
returned a CONCERN (as did the fidelity reviewer): the inequality has no counterexample, but a rigorous
proof for the ACTUAL multi-divisor terminal is not yet banked — it is the piece-6 obligation.

**PROCEED to the multi-tide build.** No re-scope of the threshold. The remaining obligation
(actual-terminal `monomialThreshold ≥ ½·minAdm`) lives in `decorated_base` (piece 6), NOT in the predicate.

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

## The genuine load-bearing case — an INEQUALITY, no counterexample (corrected post-review)

Load-bearing charts DO exist for general chains (5990 in the arity-3/4/5, widths-1..6 sweep) — e.g.
`(3,4,2)` at `t=1`: `p=2, q=3, r=min(3,2)=2, p·r=4 < 6 = minAdm`, so `c' ∈ (2,3)` is uncovered by regimes
A/B and the monomial terminal IS reached. **What is established there is the bridge INEQUALITY
`½·minAdm ≤ threshold`, NOT a tight equality** (the earlier tight-`=` framing of `(3,4,2)` was an
example-specific coincidence — corrected on review). On the `rank(Q_b)=2` chart the loss is the JOINT block
`‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²` (an isotropic Morse), whose dimension is bounded below by
`t·N_last + (N_0−t)·τ` (`τ = min` deeper widths), so its threshold is `≥ ½·(t·N_last + (N_0−t)·τ)`.

**Numeric check (`step0_ineq.py`, decisive):** across ALL `23358` load-bearing charts in the sweep, both
`N_0·τ ≥ minAdm(N)` and `t·N_last + (N_0−t)·τ ≥ minAdm(N)` hold with **ZERO** violations — so the bridge
inequality `½·minAdm ≤ threshold` has **no counterexample**. It is **NOT** always tight: `(3,4,2)` is tight
(`6 = 6`), `(4,4,2) t=1` is not (`8 > 7 = minAdm`).

**What is and is NOT banked (the reviewer's CONCERN, accepted).** `routeLayerAtlas_value`
(`RouteMLayerSplit.lean:616`, sorry-free) proves `⨅ over leaves monomialThreshold = ½·minAdm` for the
IDEALIZED SINGLE-DIVISOR atlas (each leaf = `foldDivisors [path-total]`, one divisor). It is **NOT** the
bridge on the actual accumulated MULTI-divisor terminal `monomialThreshold d (sharedDivisorExp) jac`; the
step "the actual multi-divisor threshold ≥ the idealized single-divisor value" is UNPROVEN and is the
**piece-6 obligation** (`decorated_base`). So the general uniformity is supported NUMERICALLY (the
inequality, 23358 charts, no counterexample) but is **not yet a banked Lean theorem for the actual
terminal**.

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
width (e.g. `(3,4,2)`, `(3,3,1)`); there the bridge INEQUALITY `½·minAdm ≤ threshold` has no counterexample
across 23358 sweep charts (`step0_ineq.py`), but a Lean proof for the ACTUAL multi-divisor terminal is NOT
banked (`routeLayerAtlas_value` is the idealized single-divisor model, not the actual bridge). Two
consequences:
- The predicate/decoration/peel-step build (pieces 1–5, 7) is numerically independent of the bridge value
  and proceeds unblocked; the threshold-definition decision (decoration-free `½·minAdm`) is sound.
- `decorated_base` (piece 6) carries the REAL, UNPROVEN bridge obligation: prove the actual-terminal
  `monomialThreshold d (sharedDivisorExp) jac ≥ ½·minAdm`. The numeric evidence (no counterexample) says
  this is TRUE, but it is not yet a theorem; do not treat `routeLayerAtlas_value` as discharging it.

## DATA index (exact)
- `step0_bridge.py` — per-stratum layer trace (regime classification, terminal chain, charges = minAdm).
- `step0_recurse.py` — full recursive chart enumeration; rank-deficiency flag per `(chain, cut)`.
- `step0_sweep.py` — the load-bearing condition swept over arity 3/4/5, widths 1..6; named-anchor + witness
  confirmation (all 0).
- `step0_ineq.py` — the bridge INEQUALITY check on the 23358 load-bearing charts (`N_0·τ ≥ minAdm` and the
  joint bound `t·N_last + (N_0−t)·τ ≥ minAdm`, both 0 violations); the tightness spread (not always tight).
- `codex/step0-{prompt,answer}.md` — decorrelated consult (model+verdict withheld; independent convergence
  on the load-bearing condition, the named-anchor verdict, and the `(3,4,2)` bridge — the latter tight only
  for that example, per the post-review correction).
