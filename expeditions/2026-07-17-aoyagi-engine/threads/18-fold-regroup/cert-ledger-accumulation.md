# Cert — the ledger-accumulation correspondence (the GLOBAL threaded cocycle)

*Seat: `pen-and-paper` (pnp-fold, witness), follow-up charge. Extends `cert-fold-regroup.md` §2 (the
relative-Jacobian cocycle) to the global form threaded through `buildTree`'s `stepUpdate` from `conRoot`.
Exact symbolic (`sympy` 1.14, `|·|` via `sp.Abs`, `positive=True` sources); NO Lean. Batteries
alongside (`battery/normalized_fold_verify.py`, `battery/threaded_cocycle_verify.py`, both exit-0).
Decorrelated Codex leg (`codex/threaded-cocycle-{prompt,answer}.md`, xhigh, conclusions withheld —
Codex re-derived the pullback table, the four-case maintenance, and the depth-3 run from scratch and
agreed to the component). Pinned to the LANDED t14 atoms: `geoChartMapNorm`/`diagTargetOf` (`GeoChart.lean`),
`geoChartMap_flat_pivot`/`_center`/`_spectator` + `paramsEquivFlat_geoChartMap` + `birthFlatCoord_eq_flatCoordOf`
(`GeoFoldRegroup.lean`), `geoChartMap_swap_fderiv_det` + `flatSwapCLE_abs_det_fderiv_one` (`GeoDiagSwap.lean`),
`flatSwapCLE_apply_flat` (`FlatSwap.lean`), `abs_det_fderiv_foldr_comp` (`GeoJacobianFold.lean`), `stepUpdate`
(`EngineDefs.lean:142-188`), `DivBirthInv` (`DivBirthReach.lean`). The `sorry` this discharges is
`geoAtlas_fold_det` (`GeoLeafJacobian.lean`).*

---

## VERDICTS (one line each)

- **The threaded invariant is `Inv(acc, s): |det D acc w| = L(s)(w)`**, where `L(s)(w) := ∏_{k : Fin s.numDiv}
  |z_{diagCell(s,k)}(w)|^{s.divExp k − 1}` and `diagCell(s,k) = flatCoordOf` of the divisor's `divBirthCoord`
  DIAGONAL (`= c.divCoord`, by the (β) coherence). The partial fold `acc` is the shallower (root-side)
  composite reaching state `s`; the invariant says its Jacobian modulus is `s`'s ledger monomial in the
  SOURCE coordinate.
- **Base at `conRoot`: `numDiv = 0`, `L = 1 = |det D id|`.** Every divisor of the built tree is born below,
  so the empty incoming ledger is the honest start (the `geoAtlas_fold_det` `conRoot` scope).
- **The maintenance is `L(s)(B w) · |z_{diagTargetOf}(w)|^{dCN−1} = L(s')(w)`** for the new edge chart
  `B = geoChartMapNorm (fun _ => id) e`. The crux is `L(s)(B w)` — the OLD ledger pulled back through the
  NEW chart — which supplies the case-1(2) inheritance LOCALLY. This RESOLVES the non-locality flagged in
  `cert-fold-regroup` §3: threading the full incoming ledger `L(s)` makes the inheritance a one-step fact.
- **Four cases, all verified + Codex-decorrelated:** case-2 and case-1(1) pull `L` back unchanged
  (`L(s)(B w) = L(s)(w)`); case-1(2) scales the u-corner (`L(s)(B w) = |z_{diagTargetOf}(w)|^{divExp(mergeIdx)−1}
  · L(s)(w)`); rollover is chart- and ledger-neutral (`B = id`, `L(s') = L(s)`).
- **No kill-condition remains.** The t14 diagonal normalization (`geoChartMapNorm = geoChartMap ∘ S`,
  `S = flatSwapCLE(cNodeOf pivot, diagTargetOf)`) relocates every exceptional divisor to its diagonal, so
  birth-cell = reference-cell = diagonal for every fan-out pivot — the `cert-fold-regroup` §4 off-diagonal
  discrepancy cannot arise (re-confirmed on the actual swap-composed charts, `normalized_fold_verify.py`).

---

## §1 The threaded invariant

For a state `s` (a `ConState L` reachable in `buildTree M (conOracle M) conRoot`) and a partial-fold
accumulator `acc : Params M → Params M` (the composite of the diagonal-normalized charts along the path
from `conRoot` down to `s`, root outermost):

    Inv(acc, s) : Differentiable ℝ acc ∧
                  ∀ w, |(fderiv ℝ acc w).det|
                        = ∏ k : Fin s.numDiv, |paramsEquivFlat M w (diagCell M s k)| ^ (s.divExp k − 1)

writing `L(s)(w)` for the RHS product and `diagCell M s k := birthFlatCoord M s k _` (the diagonal
`flatCoordOf` of `s.divBirthCoord k`, which is `c.divCoord k` by the (β) coherence
`birthFlatCoord_eq_flatCoordOf`).

- **Base (`s = conRoot`, `acc = id`):** `s.numDiv = 0`, so `L(conRoot) = 1`; `|det D id w| = 1`. `Inv(id, conRoot)`.
- **Headline (`geoAtlas_fold_det`):** at a leaf, `acc = c.chartMap` (the baked full fold, `tGeo_coherence`)
  and `s = leaf state`. `Inv(chartMap, leafState)` gives `|det D c.chartMap w| = L(s)(w)` over the FULL
  state ledger `s.numDiv`. **CORRECTION (`cert-stranded-dichotomy.md`, supersedes):** the RHS is the FULL
  ledger (`fullNumDiv`/`fullDivExp` + a `fullDivCoord`), NOT `leafOfState`'s analytic `c.numDiv`/`c.divExp`.
  Reachable terminals carry stranded (t̃>0) divisors with `divExp > 1` (witness `M=(2,3)`), so the analytic
  RHS is FALSE and `geoAtlas_fold_det` (`GeoLeafJacobian.lean:39`) must be restated to the full ledger.
  The cocycle here is already full-ledger (`L(s)` sums over `s.numDiv`); only the leaf STATEMENT changes.
  The stranded factors are RLCT-inert (`cert-stranded-dichotomy` §4), so the analytic ledger stays the
  read for the loss / C-agreement / RLCT pole.

The invariant threads DOWN the tree (mirrors `tGeo`/`tGeo_composite_differentiable`, which already threads
`acc` and proves the `Differentiable ℝ acc` half at every leaf). The maintenance below carries the
determinant equality alongside.

## §2 The normalized chart's coordinate action + the per-edge atom

Let `B = geoChartMapNorm (fun _ => id) g` for an on-cone edge (`hd : dCenterOfNode M node ≤ flatDim M`,
`hp : pivot < dCenterOfNode M node`). By `geoChartMapNorm_apply_oncone`, `B = geoChartMap g ∘ flatSwapCLE M p d`
with `p = cNodeOf M node hd ⟨pivot⟩` (the fan-out pivot cell) and `d = diagTargetOf M node edge`. Composing
the (α) reads (`geoChartMap_flat_pivot`/`_center`/`_spectator`) with `flatSwapCLE_apply_flat`
(`z_c(S w) = z_{swap p d c}(w)`) gives the full flat action (Codex Q1; `normalized_fold_verify.py`):

    z_c(B w) = z_c(w)                    if c ∉ center C(node)           -- spectator
             = z_d(w)                    if c = p                        -- pivot cell carries the exceptional value
             = z_d(w) · z_p(w)           if c = d  (≠ p)                 -- diagonal cell (a non-pivot center cell)
             = z_d(w) · z_c(w)           if c ∈ C(node) \ {p, d}         -- other center cells

**The per-edge atom** (`geoChartMap_swap_fderiv_det`, via `abs_det_fderiv_comp_det_one_gauge` on `S`
det-1 + `geoChartMap_fderiv_det`): `|(fderiv ℝ B w).det| = |z_d(w)|^{dCenterOfNode M node − 1}` — the
exceptional divisor is read at the DIAGONAL `d = diagTargetOf`. (`dCenterOfNode − 1 = runLen·resCols` for
case-1, `= resRows·resCols − 1` for case-2.)

`diagTargetOf` (per `GeoChart.lean:58`): case-1(1) ⟹ `mergeIdx`'s `divBirthCoord` diagonal (there `p = d`,
so `S = id`); case-1(2)/case-2 ⟹ the `(layer, cleared)` diagonal (the born divisor's birth corner).

## §3 The four per-`stepUpdate`-case maintenance identities (Lean-ready)

Each closes `L(s)(B w) · |z_{diagTargetOf}(w)|^{dCN−1} = L(s')(w)` where `s' = ` the child state (`s`'s
ledger updated by `stepUpdate`). Write `μ = diagCell(s, mergeIdx)` (the merged divisor's diagonal) and
`e = s.divExp mergeIdx`; `b := dCenterOfNode M node − 1`.

**det-only vs value-carrying (for the §7 second consumer).** In each case the ingredients split: the
coordinate-action reads `geoChartMap_flat_{pivot,center,spectator}` + `flatSwapCLE_apply_flat` are
**VALUE-CARRYING** (the same reads drive how `prod ∘ chartMap`'s entries transform); the scalar Jacobian
atom `|z_{diagTargetOf}|^{dCN−1}`, `|det|`-multiplicativity (`clm_det_comp`), and the `divExp − 1`
exponent arithmetic are **DET-ONLY** (a derivative fact the value never sees). The tree-walk / per-case
dispatch / `conRoot` base / `DivBirthInv` threading is **SHARED SKELETON**.

**(1) case-2** (`stepUpdate.case2`: appends a divisor, `divExp = resRows·resCols`; `dCN = resRows·resCols`).
- `d = diagTargetOf` is the fresh `(layer,cleared)` diagonal; the center `C(node)` is the fresh residual
  block. Every EXISTING divisor's diagonal `diagCell(s,k)` is `∉ C(node)` and `≠ d` — from `DivBirthInv`
  freshness (existing diagonals at `layer` have col `< cleared`, the block sits at col `≥ cleared`) +
  layer-bound + injectivity. So each is a spectator: `z_{diagCell(s,k)}(B w) = z_{diagCell(s,k)}(w)`
  (`geoChartMap_flat_spectator` + `flatSwapCLE_apply_flat` with `c ∉ {p,d}`).
- Hence `L(s)(B w) = L(s)(w)`, and `L(s')(w) = L(s)(w) · |z_d(w)|^{resRows·resCols − 1}` (the appended
  divisor at `d`). Maintenance: `L(s)(w) · |z_d(w)|^{b} = L(s')(w)`. **CLEAN.**
- Lean shape: `geoChartMap_flat_spectator` (each old divisor cell), the fresh-vs-old disjointness from
  `DivBirthInv`, `Fin.prod_snoc`/`Finset.prod` append for the new divisor.

**(2) case-1(1)** (`stepUpdate.case11`: `divExp(mergeIdx) += runLen·resCols`, no new divisor; `dCN =
1+runLen·resCols`). `p = d = μ` (the u-corner IS the pivot; `S = id`).
- `μ` is the pivot: `z_μ(B w) = z_d(w) = z_μ(w)` (`geoChartMap_flat_pivot`, `d = μ`). All other existing
  divisors `∉ C(node)` (their diagonals ≠ μ by injectivity, ∉ fresh d-block by freshness) — spectators.
  So `L(s)(B w) = L(s)(w)`.
- `L(s')(w) = L(s)(w) · |z_μ(w)|^{b}` (the mergeIdx factor's exponent grows by `b = runLen·resCols`).
  Maintenance: `L(s)(w) · |z_μ(w)|^{b} = L(s')(w)`. **RE-MERGE onto `μ`** (the mergeIdx diagonal, `= c.divCoord`).
- Lean shape: `geoChartMap_flat_pivot` for `μ`, `_spectator` for the rest; the `stepUpdate.case11` `if
  (k:ℕ) = mergeIdx` exponent bump reindexed onto the same `Finset.prod` (one factor changes exponent).

**(3) case-1(2)** (`stepUpdate.case12`: appends a divisor, `divExp = divExp(mergeIdx) + runLen·resCols`,
mergeIdx unchanged; `dCN = 1+runLen·resCols`). `p` = a fresh d-block cell (fan-out pivot), `d = diagTargetOf`
= the new divisor's fresh d-block diagonal; `μ` (u-corner) `∈ C(node) \ {p, d}`.
- `μ` is a non-pivot center cell, `μ ∉ {p,d}` (u-corner distinct from the fresh d-block cells, by
  freshness/injectivity): `z_μ(B w) = z_d(w) · z_μ(w)` (`geoChartMap_flat_center` + `flatSwapCLE_apply_flat`,
  `c ∉ {p,d}` on both `z_p(S w)=z_d(w)` and `z_μ(S w)=z_μ(w)`). Every OTHER existing divisor is a spectator.
- Hence `L(s)(B w) = |z_d(w)|^{e − 1} · L(s)(w)` (the mergeIdx factor `|z_μ|^{e−1}` becomes
  `|z_d · z_μ|^{e−1} = |z_d|^{e−1} · |z_μ|^{e−1}`, spawning the inheritance `|z_d|^{e−1}`). And
  `L(s')(w) = L(s)(w) · |z_d(w)|^{(e + b) − 1}` (the appended divisor at `d`, `divExp = e + b`).
  Maintenance: `|z_d|^{e−1} · L(s)(w) · |z_d|^{b} = L(s)(w) · |z_d|^{(e+b)−1} = L(s')(w)`.
  **INHERITED-THREADING, made LOCAL by `L(s)(B w)`.**
- Lean shape: `geoChartMap_flat_center` for `μ` (the ONE scaled ledger cell), `_spectator` for the rest;
  `flatSwapCLE_apply_flat` twice; the appended-divisor `Fin.prod_snoc`; the exponent arithmetic
  `(e−1) + b = (e+b) − 1` by `omega` (needs `e ≥ 1`, i.e. `divExp(mergeIdx) ≥ 1` — true for a live divisor,
  from the ledger's positivity / `IsFullMonomialization`; flag as a side condition).

**(4) rollover** (`stepUpdate.rollover`: ledger carried verbatim, only `cleared := 0`; the fanned edge is
CHARTLESS, `localSub := id`, `acc' = acc ∘ id = acc`).
- No chart (`B = id`), atom `= 1`; `s'` has the SAME `numDiv`/`divExp`/`divBirthCoord` (`DivBirthInv_stepRollover`),
  so `diagCell` and `L` are unchanged: `L(s') = L(s)`. `Inv(acc, s) ⟹ Inv(acc, s')` immediately.

## §4 sympy verification (`battery/`, all exit-0)

- `threaded_cocycle_verify.py` — a depth-4 MIXED run + rollover + a post-rollover second birth
  (case-2 A → case-1(2) split B off A → case-1(1) merge A → case-1(1) merge B → rollover → case-2 births C),
  tracking `L(s_i)` at every state. Confirms BOTH the per-step maintenance `L(s)(B w)·atom = L(s')(w)`
  (all 6 steps PASS, incl. rollover-neutrality) AND the cumulative `|det D Φ^{(i)}| = L(s_i)` at every
  prefix (all 6 PASS). The case-1(2) step shows `L(s_prev)(B w)·atom = z_dA^3·z_dB^5 = L(s_new)`, the
  inheritance appearing through the pulled-back u-term.
- `normalized_fold_verify.py` — the ACTUAL swap-composed charts `geoChartMap ∘ S`: every divisor lands on
  its diagonal for ALL fan-out pivots (N1–N5, incl. the exact shape that broke un-normalized in
  `cert-fold-regroup` §4, now PASS via `S`), confirming t14's kill-condition dissolution. `|det|` via
  `sp.Abs` (the swap `S` is a transposition, `det S = −1`; the atom uses `|det|`).
- The `cert-fold-regroup` batteries (`fold_regroup_verify.py` etc.) remain the un-normalized ground truth.

## §5 Codex decorrelation (`codex/threaded-cocycle-{prompt,answer}.md`, xhigh, conclusions withheld)

Given only the chart model + the recursion (my invariant + verdicts withheld), Codex independently
derived: Q1 the four-row coordinate pullback table (identical to §2) and the per-case `L(s)(B w)`; Q2 the
edge identity `L(s)(B w)·|det DB| = L(s')(w)` for every edge, noting for case-1(2) that "`|z_d|^{e−1}`
comes from pulling back the old u-term … not from the new divisor or directly from the chart determinant"
(= §3(3), the locality resolution); Q3 the propagation with the exact hypothesis list (functional identity
at `B(w)`, the normalized-chart det, freshness, `u ∉ {p,d}`, composition order `acc ∘ B`); Q4 the depth-3
run giving `|z_a|^3 · |z_b|^6 = L_3`. Two decorrelated derivations agree to the component.

## §6 Transcription notes (for t14 — the induction skeleton)

- **Motive** (mutual, mirroring `tGeo_composite_differentiable`): for `acc` reaching state `s`,
  `Inv(acc, s)` (§1) — `Differentiable ℝ acc` (already banked at every leaf) AND `∀ w, |det D acc w| =
  L(s)(w)`. Carry `DivBirthInv M s` as a threaded hypothesis (supplies freshness/injectivity/validity for
  the §3 disjointness reads; already threaded by `DivBirthInv_conOracle_stepChildren`).
- **Base**: `Inv(id, conRoot)` — `numDiv = 0` ⟹ `L = 1`, `fderiv_id` ⟹ `|det| = 1`.
- **Step** (one per `stepUpdate` case, §3 shapes): `Inv(acc, s) → DivBirthInv M s → StepRel n e →
  Inv(acc ∘ geoChartMapNorm (fun _ => id) ⟨n, e, offset+p⟩, s')`, `s'` the child. Each consumes
  `abs_det_fderiv_comp_det_one_gauge` (chain rule + `S` det-1, giving `|det D acc' w| = |det D acc (B w)|
  · |z_d(w)|^{dCN−1}`) then the §3 case identity for `L(s)(B w)` via `geoChartMap_flat_{pivot,center,spectator}`
  + `flatSwapCLE_apply_flat`. Use the LANDED `abs_det_fderiv_foldr_comp` for the list-fold framing, or the
  direct `acc ∘ B` chain-rule step above (the latter matches `tGeo`'s acc-threading more closely — either
  works; the acc-threaded form avoids materializing the intermediate-point list).
- **Assembly to `geoAtlas_fold_det`**: at a leaf, `acc = c.chartMap` (`tGeo_coherence`), `s = leaf state`,
  `c.divExp = s.divExp`, `c.divCoord k = diagCell M s k` (`birthFlatCoord_eq_flatCoordOf`, the (β)
  coherence). Instantiate `Inv` at the leaf; `conRoot` gives the empty incoming ledger.
- **Side conditions to gate** (all discharged by the reachability supply, none open math):
  (i) on-cone throughout (`dCenterOfNode ≤ flatDim`, `dCenterOfNode_le_flatDim`; pivot in range from the
  fan-out `finRange`); (ii) `DivBirthInv` freshness/injectivity for the §3 disjointness (existing diagonals
  ∉ fresh block, `μ ∉ {p,d}`, distinct diagonals); (iii) `divExp(mergeIdx) ≥ 1` for the case-1(2) `omega`
  step (a live divisor's exponent is `≥ 1`; from `IsFullMonomialization`/`Mval ≥ 1`). No off-diagonal
  discrepancy: the swap `S` guarantees `diagTargetOf = diagCell` (birth = reference), so §3 never needs a
  per-pivot divCoord — the `cert-fold-regroup` §4 kill-condition is structurally excluded by
  `geoChartMapNorm`.

## §7 The value-level second consumer (loss-t15) and the DELTA

loss-t15 reduces `LeafPullback` to the named input `prod M (chartMap w) = diagonal(monomial chain)` at
each leaf — Aoyagi's `Q · prod · P = diag(b₁,…,b_m)` invariant (`cert-loss-factorization.md`). This is
the loss-VALUE analog of the det correspondence. **Verdict: same SKELETON, different CONTENT; the det is
NOT derivable from the value, and one cert does not fully serve both.** (Consistent with the sibling
`cert-loss-factorization` §Structure: "LeafPullback (power-2) and LeafJacobian (accumulated) do NOT share
the fold induction.")

**Why not derivable (three divergent exponent structures).** A single divisor `A` under a case-2 birth
`+ k` case-1(1) re-merges carries THREE different exponents (`value_vs_det_delta.py`, exact):

| read | object | `A`-exponent | behaviour under re-merge |
|---|---|---|---|
| **DET** (this cert) | `|det D chartMap|` | `divExp(A) − 1 = 3 + k` | **accumulates** |
| **VALUE** diag-monomial `b₁` | `prod ∘ chartMap = diag(b)` | `1` (squarefree, `b₁ = ∏_{t̃=0} u`) | does NOT accumulate |
| **LOSS** | `frobSq = (∏ divCoord²)·core` | `2` (uniform) | does NOT accumulate |

The accumulation `divExp − 1` is a change-of-variables (derivative) count, invisible to the value's
`b₁` (each terminal divisor once) and to the power-2 loss. So `|det D chartMap|` cannot be read off
`prod ∘ chartMap`.

**What IS shared (the value cert reuses this verbatim).** The threaded-induction SKELETON — the
`tGeo`/`geometricLeafPaths` tree walk, the per-`stepUpdate`-case dispatch, the `conRoot` base, the
`DivBirthInv` threading — AND the coordinate-action reads (`geoChartMap_flat_{pivot,center,spectator}` +
`flatSwapCLE_apply_flat`): the value maintenance uses the SAME reads to track how each entry of `prod`
transforms across a blow-up. The value invariant states naturally in the SAME acc-threaded form
`Inv_val(acc, s): prod M (acc w) = diag(b(s))·[[E_J,O],[O,D_J(residual coords)]]` (Aoyagi's state
invariant), with the SAME motive shape and base (`prod M (id w) = ∏ C^{(s)}` at `conRoot`).

**The DELTA (value-only content the det never sees).**
1. **The residual / off-diagonal block `D_J`.** The value carries the full matrix, so its maintenance
   tracks the un-resolved block (the ratio coordinates `d'_{ij}`), not only the diagonal divisor cells.
   The det collapses this to a scalar and never sees it.
2. **The `b_i` are PRODUCTS (power 1), not `divExp` powers.** `b₁ = ∏_{t̃=0} u`, `bᵢ/bᵢ₋₁ = ∏_{born at
   level i−1} u` — a different ledger read than `divExp` (the value cert tracks the `b`-chain; the det
   tracks `divExp`).
3. **The incidence / Q,P Schur source gauge.** Reducing the block to `[[1,O],[O,D_{J+1}]]` needs the
   det-1 ratio shear `α` (`z ↦ z − r_ip·r_pj`). The Jacobian is **det-1-BLIND** to it (`ShearReconcile`:
   `det Dψ = 1`), so §1–§6 omit it entirely; the value is NOT det-1-blind (Frobenius changes under Q,P),
   so `Inv_val`'s maintenance MUST carry `α`. This is the "one fix does not serve both" of
   `cert-loss-factorization` §6: the det needs only the fork-15 diagonal swap `S`; the value needs `S`
   AND the Schur `α`.
4. **`resRank`/`resCoord` matching the actual leaf residual shape** (Morse vs fully-diagonal;
   `cert-loss-factorization` §Structure / task #42) — a value-side obligation the det does not carry.

**Value battery (the depth-4 value run).** `battery/value_threaded_verify.py` (exit-0) tracks `prod`'s
VALUE = `diag(b)` through the SAME depth-4 scenario as the det (`threaded_cocycle_verify.py`): Part A —
the `b`-chain threaded per state (`b₁ = ∏` terminal, loss `= ∑ bᵢ²`, `b₁` squarefree, residual free of
terminal, all 6 states PASS); Part B — the DET-vs-VALUE contrast on one run (`|det| = z_A⁴` accumulated
vs `b`-power 1 vs loss-power 2, confirming non-derivability); Part C — the delta on actual matrices: the
incidence residual `u·[[1,a],[b,ab+ρ]]` has off-diagonal `(a·u, b·u)` that only the **det-1** Q,P Schur
gauge (`Lg·prod·Rg`) clears to `diag(u, ρu)` — a value-only reduction the det (`|det Lg| = |det Rg| = 1`)
is blind to.

**Recommendation.** Keep TWO certs (this det cocycle + `cert-loss-factorization` for the value/loss),
sharing the SKELETON explicitly. When t14/loss-t15 transcribe, factor the shared skeleton
(tree-walk + per-case dispatch + `DivBirthInv` + the `geoChartMap_flat_*` reads) into a reusable
induction driver, then instantiate it TWICE: once with the scalar det payload (§3), once with the
matrix `diag(b)·D_J` payload + the `α` gauge (the value delta). The value delta (points 1–4) is genuinely
its own content and is already adjudicated in `cert-loss-factorization` — no new paper work owed there.

## Close

- **Firmest (battery-verified + Codex-decorrelated):** the threaded invariant `Inv(acc, s)` (§1); the
  normalized coordinate-action table + diagonal atom (§2); the four per-case maintenance identities (§3),
  each Lean-ready and keyed to a landed t14 atom; the base at `conRoot` (`L = 1`).
- **Second consumer (§7):** the value invariant `prod ∘ chartMap = diag(b)` shares this cert's threaded
  SKELETON + coordinate-action reads but tracks different content (the `b`-chain + residual block + the
  Schur `α` gauge); the det is NOT derivable from it (three divergent exponent structures). Two certs,
  one shared driver.
- **Most likely to break it:** a gap in the reachability supply (§6 side conditions) — specifically if the
  `DivBirthInv` freshness/injectivity is not threaded to EVERY step of the fold (the disjointness reads in
  §3(1)/(3) fail without it), or if a `divExp(mergeIdx) = 0` live divisor slips through (breaks the
  case-1(2) `omega`). Both are reachability facts already owned by the carrier, not new math.
- **Next:** the cocycle is fully specified; the remaining work is the Lean transcription of the §6
  skeleton (t14's lane). No further paper adjudication is needed — §1–§3 pin the invariant and its
  maintenance exactly, and §4/§5 double-verify.
