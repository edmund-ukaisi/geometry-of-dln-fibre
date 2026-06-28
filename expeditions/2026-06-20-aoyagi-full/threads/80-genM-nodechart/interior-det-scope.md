# #3 INTERIOR chart cov/det — precise scope assessment (the heaviest branch)

**Task:** discharge `hInterior : ∀ 2≤L, InteriorDrop M → BoxDiverges` — the interior branch's
box-divergence, via the colPath Schur chart's `cov` (`|det Dφ| = ∏_j |u_j|^{leafH j}`, injOn, the
n-fold null-slice). **Finding: BOUNDED but a major multi-tide build with a genuine design dimension —
NOT a one-tide grind. The bricks are banked; the assembly is large.**

## Why interior is NOT single-pivot-reducible (unlike clean/smeared)

The smeared/clean branches route through `of_RadialMPChart`: ψ (the non-radial part) is
MEASURE-PRESERVING (det 1) so the radial `R` is the SOLE Jacobian carrier → single-pivot
`|u_p|^{minAdm−1}`. The interior branch CANNOT: the Schur-frame `K`-core blocks are FREE coordinates
(read from `x` via `readK`), so the frame Jacobian is `∏_s |det K_s|^{r_s+c_s}` (`schurFrame_abs_det`,
banked) with `det K_s` VARYING with `x` — multi-axis, NOT det-1. Confirmed structurally: `(3,3,3,3)`
(an INTERIOR node) has `|det Dφ| = |u0|⁵·|u1|⁴·|u4|²·|u9|³` (four axes; the `(z1·z4−z2·z3)²` block is
`|det K₁|²`). So the interior `leafH` is genuinely MULTI-AXIS and construction-sensitive.

## The design crux: `det K_s` must be a MONOMIAL for the `cov` form

`NodeAchieverChart.cov` requires `|det Dφ| = ∏_j |u_j|^{leafH j}` — a pure MONOMIAL. But `det K_s`
(e.g. `z1·z4−z2·z3`) is a POLYNOMIAL, not a monomial. The `(3,3,3,3)` anchor resolved this by an LDU
coordinatization of each K-core so `det K = ∏ (LDU pivots)` = a monomial in the pivot coords (the
banked `lduCoreDeriv_det = ∏ q_i^{2(t−1−i)}`). So the general interior chart MUST coordinatize each
K-core via LDU; then `leafH` is the multi-axis monomial in the radial + the per-boundary LDU pivots.

## The banked bricks (all sorry-free) — the build IS reachable from them
- `schurFrame_abs_det` (`RouteMSchurFrameDet`): `|det DS| = |det K|^{r+c}` per boundary. ✓
- `lduCoreDeriv_det` (`RouteMSchurFrameDet`/r1-genA): `det(LDU core) = ∏ q_i^{2(t−1−i)}` — the K-core
  monomial coordinatization. ✓ (gated — verify the gate's hyps hold for the interior path)
- `composeFold_abs_det_leafH` (mine, `RouteMPhiFlatDet`): the variable-length telescope
  `|det D(composeFold fs)| = ∏|u_j|^{leafH j}` GIVEN the per-factor det bookkeeping. ✓
- `pivotBlowupOn` det/injOn (the radial). ✓
- `routeMCore_phiFlatStructV` (rate `u_p²·U` ∀M), `achieverUbound_interior` (U≢0 a.e.), banked. ✓

## The OPEN build (the major work, in order)
1. **The LDU coordinatization of `genBlkFlatStruct`'s K-cores** so each `det K_s` is a monomial —
   either re-coordinatize `readK` to LDU pivots, or compose an LDU change-of-coords. (Design choice;
   the `(3,3,3,3)` `Kparam3333` is the template, but general-L/opaque-width.)
2. **Item-3 map equality** `phiFlatStructV (interior) = composeFold [radial, schurFrame_s, lduCore_s …]`
   over the variable-length descent path — THE bottleneck (the structured chart is defined via `phiGen`,
   not `composeFold`; bridging them over opaque `Wext`/`Text` widths is the hard dependent-cast work).
3. **The multi-axis `leafH`** = the radial `minAdm−1` on the pivot + the LDU-pivot exponents
   `2(t−1−i)` + the frame `r_s+c_s` exponents; `leafH_pivot : leafH p = minAdm−1` (the others are
   spectators, `k=0`, don't lower the threshold — `nodeChart_thresholdLe` already handles that).
4. **injOn off the union of weighted-axis planes** + the **n-fold null-slice cov** (generalising the
   `(3,3,3,3)` 4-slice `phi3333_cov` to the variable weighted-axis count).

## Verdict + recommendation
- **NOT a wall** (every brick is banked; the `(3,3,3,3)` anchor is the complete worked instance), but a
  **MAJOR multi-tide build** (item-2 the variable-length map equality is the genuine design dimension —
  the same dependent-`Fin`-cast fight that cost tides on the `(2,2,2)`/`(3,3,3,3)` det bridges, now
  over opaque widths). NOT completable in one tide; NOT honest to open it as a single grind.
- **Smallest de-risking increment I can land now:** an INTERIOR-branch CONTRACT (mirroring the smeared
  `routeMCore_box_diverges_smearedContract`): the M-agnostic statement that GIVEN the interior chart's
  factored fderiv + the per-factor LDU/frame/radial dets (the item-2/3 outputs), the box-divergence
  follows — isolating the item-2/3 map-equality + det-bookkeeping as the precise remaining obligation.
  This banks the spine for the interior branch (parallel to what the smeared contract did) without the
  multi-tide chart construction.
- **Bigger-than-one-tide pieces (roadmap, for the controller's scope call):** item-1 (LDU
  coordinatization ∀M), item-2 (the `composeFold = phiFlatStructV` map equality over opaque widths),
  item-4 (the n-fold null-slice cov). These are the genuine interior build, each a substantial tide.
