# GATE verdict — ∀M-L2 interior monomial chart: BOUNDED (major), NOT a wall

The team-lead's GATE-FIRST ask: bounded-vs-wall on the `composeFold = phiFlatStructV` map-equality
over opaque widths + the n-fold null-slice `cov`, before the heavy build. **Verdict: BOUNDED on
both risk loci (R1 map-eq/det, R2 cov), a major multi-tide build. PROCEED with sub-hands.** Codex
(xhigh) independently: R1 BOUNDED-BUT-MAJOR, R2 BOUNDED-BUT-MAJOR, proceed-with-sub-hands.

## What is ALREADY banked (much more than thread-80 recorded)

The det-side bridge is **further along than thread-80's "items 1–4 open"**:

- **The det telescope** `composeFold_abs_det` + the GENERIC target lemma `phiTarget_abs_det_of_factored`
  (`RouteMPhiTargetDet`): for `phi := phiFlatStructV`, GIVEN a factor list `fs` with `composeFold fs =
  phi` and the per-factor det bookkeeping, `|det Dφ| = ∏|u_j|^{leafH_j}`. Sorry-free.
- **The per-factor maps + dets** (`RouteMFactorMaps`): Schur `|det DS|=|det K|^{r+c}`, LDU
  `|det|=∏|q_i|^{2(t−1−i)}`, chain `|det|=1`, radial `|det|=|u_p|^{minAdm−1}` — all full-ambient
  `ChartFactor`s, sorry-free.
- **The CLE-collapse bridge spine** (`RouteMBridgeCLE`): `composeFold fs = phiFlatStructV` is REDUCED
  (sorry-free) to a Params-level layer-op equality via `bridgeCLE`; `composeFold_bridge_eq` +
  `phiParamsStruct_bridgeCLE` close the alignment by CLE cancellation (no per-index proof). Mechanism
  validated end-to-end (monolithic op).
- **THE LDU STRAIGHTENING ∀M** (`RouteMKLens`, the hardest R1 sub-step Codex named): `kLDU` ∀M +
  `readK_kLDU_det : det(readK(kLDU x) k) = ∏_i (matrixSplit (readK x k)).2.1 i` — the free-K det
  (a degree-t polynomial) replaced by the diagonal-pivot MONOMIAL, over OPAQUE widths. Sorry-free.
  This is thread-80 item 1 — DONE.
- **The factor-fold→real-chart route validated** on `(4,4,2,2)` (`RouteM4422Bridge`,
  `phi4422_eq_composeFold` + `phiTarget_abs_det_of_factored`) — the clean (linear+radial) anchor,
  end-to-end sorry-free.

## Exponent arithmetic — VERIFIED consistent (numeric, this thread)
The multi-axis `leafH = radial(minAdm−1) ⊕ per-boundary[(r+c) + 2(t−1−i)]` reproduces the worked
`(3,3,3,3)` `leafH3333 = |u0|⁵·|u1|⁴·|u4|²·|u9|³` exactly (radial 5=minAdm−1; 2×2 core boundary
r+c=2 → {4,2}; 1×1 core boundary r+c=3 → {3}). The geometry generalizes cleanly.

## What remains OPEN (the genuine build, all BOUNDED)
1. **The interior layer-op list `gs : List (Params M → Params M)`** for the LDU-lensed structured
   decoder + its `composeFold_bridge_eq` discharge: decompose `phiParamsStruct` (on `kLDU`) into the
   dependency-ordered Schur_s/LDU_s/chain_s/radial fold. The spine + per-factor maps are banked; this
   is the ordered assembly + the `funext s` per-layer match (the opaque-width cast fight — the
   `lean/CLAUDE.md` `chainA`/dependent-width quirk, bounded, costed two tides on anchors).
2. **The multi-axis `leafH` det bookkeeping** `∏|det D_i| = ∏|u_j|^{leafH_j}`: assemble the banked
   per-factor dets through `readK_kLDU_det` + the exponent arithmetic above. Bounded.
3. **The `cov` lintegral c-o-v** (R2): injOn off the weighted-axis planes + the n-fold null-slice,
   generalizing `phi3333_cov`'s 4-slice template to the variable axis count. Codex: bounded via
   finite-union nullity / finite induction; major because it must compose with the bridge + off-axis
   injOn. The weighted-axis set is finite & decidable per M.
4. **Wire** the four `routeMCore_box_diverges_interiorContract` fields (`leafH`, `hleafH_pivot`,
   `hUmeas`, `hcov`, `himage`) → the L=2 `hInterior` atom. (Rate + Ubound + leaf_integrand already
   banked for `phiFlatStructV`; NB if the chart switches to the `kLDU`-lensed decoder the rate must be
   re-confirmed on `phiFlatLDU` — `routeMCore_phiFlatLDU` is noted banked in `RouteMKLens` docstring.)

## Recommendation
PROCEED (option a), **with sub-hands** — it is a major multi-tide build. Natural decomposition into
parallelizable sub-hands: (H1) the interior layer-op list `gs` + `composeFold_bridge_eq` discharge
(the cast-heavy bottleneck); (H2) the multi-axis `leafH` + det bookkeeping (mechanical given H1 + the
banked atoms); (H3) the n-fold null-slice `cov` (R2, independent of H1/H2 once `fs` is fixed). I drive
H1 (the spine I own) + the final contract wiring + the achiever assembly; H2/H3 are commissionable.
No wall found. No canonical edits; baseline green.
