# genm-r1lower STEP-0 verdict — the eihd det does NOT feed the R1-LOWER interior `hcov`

**Branch:** `expedition/genm-r1lower` off canonical `25df8e80` (clean, baseline build green,
8349 jobs). **Mission framing (from team-lead):** discharge the L=2 INTERIOR `hcov` of
`routeMCore_box_diverges_interiorContract` using the just-landed
`interiorDet_leaf_headline_eihd`. **Verdict: that premise is FALSE — STOP before the heavy build.**

## Two independent gates of STEP-0 both FAIL

### Gate 1 — chart identity (decoder mismatch)
- The interior contract (`RouteMInteriorContract.lean:46`) wires `achieverPhi M hL hN`, which is
  `phiFlatStructV` — the **DEAD-LEAF / structured** decoder (`RouteMAchieverRateFields.lean:47`).
- `interiorDet_leaf_headline_eihd` (`RouteMHDtotEihd.lean:1029`) is for `phiFlatLiveAt M ha _
  (leafPivot …)` — the **LIVE-LEAF** decoder (`RouteMLeafChart.lean:70`, `genBlkFlatLive` keeps the
  leaf E-block angular coords; the structured decoder zeroes them).
- These are provably different decoders. There is **no** banked det (monomial or otherwise) for
  `phiFlatStructV`/`achieverPhi` at all (grep: zero hits for `phiFlatStructV.*det`). The eihd det
  cannot discharge a `cov` field about a different chart.

### Gate 2 — Jacobian shape (non-monomial vs monomial)
- `NodeAchieverChart.cov` (`NodeAchieverChart.lean:99`) demands a **pure monomial** Jacobian
  `|det Dφ| = ∏_j |u_j|^{leafH_j}`.
- The eihd det gives `|det Dφ_live| = |u_p|^{minAdm−1} · |det(leafKcore)|^{r+c}`
  (`RouteMHDtotEihd.lean:1034`, with `∏ engineFreeK = |det leafKcore|^{r+c}`,
  `RouteMLeafEngine.lean:66`). `leafKcore = readK` is a free Schur-core matrix block — its
  determinant is a **polynomial, not a monomial**. So the eihd det is NOT in the `cov` form.
- The worked monomial-Jacobian interior anchors solve this by an LDU coordinatization that
  STRAIGHTENS `det K` into a monomial: `phi3333` uses `Kparam3333` (`z1z4−z2z3 ↦ u1·u4`) to get
  `|det Dφ_3333| = |u0|⁵·|u1|⁴·|u4|²·|u9|³` (`RouteM3333Atom.lean:513`). The eihd det does NOT
  perform that straightening — it reports the free-K det as-is.
- Even at the small case the exponents DISAGREE: at the `(3,3,4)` interior boundary the eihd det's
  K-exponent is `r+c = 4`, whereas the worked monomial chart `phi334` puts exponent `2` on that
  axis (`leafH334 = (7,2,0,…)`, `RouteMLayerCoverGEL2.lean:166`). Different chart geometries.

### Decorrelated Codex (xhigh) — corroborates, independently
`codex/step0-chart-identity-{prompt,answer}.md`: **Q1 WRONG-VEHICLE**, **Q3 YES-SEPARATE-BUILD**.
Folding `|det K|^{r+c}` into a bounded unit `U` is NOT measure-theoretically sound (`det K` can
vanish, so `U·|det K|^{−(r+c)}` is unbounded); zeroing the spectator `leafH` and pretending the
Jacobian is `|u_p|^{minAdm−1}` only is unsound for the EXACT `cov` identity (the live det genuinely
carries the extra factor). The eihd det belongs to the **D1 UPPER-bound** IFT route
(`rlctAtOn_eq_of_contDiff_chart`, `S1IFTChart.lean:225`), not the R1-LOWER box-divergence.

## What the interior R1-LOWER leg actually needs (unchanged from thread-80)
A separate **pure-monomial-Jacobian** chart for ∀M-L2 (phi3333/LDU-style), i.e. thread-80's open
items 1–4 (`interior-det-scope.md`): LDU coordinatization of `genBlkFlatStruct`'s K-cores;
the `composeFold = phiFlatStructV` map equality over opaque `Wext`/`Text` widths (the genuine
bottleneck); the multi-axis `leafH`; the n-fold null-slice `cov`. The eihd det advances none of
these — it is the live-chart, free-K Jacobian.

## Smeared branch (the OTHER `2≤L` atom) — eihd det also irrelevant
`routeMCore_box_diverges_smearedContract` routes through `of_RadialMPChart`: the radial blow-up is
the SOLE Jacobian carrier (clean single-pivot monomial `|u_p|^{minAdm−1}`), the rational shear is
measure-preserving (det 1). The eihd interior det does not enter. The per-family bricks
(`RouteMSmearedPerFamily.lean`: det/inv measurability, `measurePreserving_shearM`,
`smearedSubBox`) are banked; the smeared L=2 close is a per-family `ψ/R/S` build, independent of
the eihd det.

## Bottom line
The directed task ("discharge interior `hcov` from the eihd det") rests on a false premise. The
eihd det is sound and useful — but for the D1 UPPER route, not R1-LOWER. Surfaced to team-lead;
NOT fake-closing. No edits to canonical made.
