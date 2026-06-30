# deepRank=0 interior handler (#250) — build state + item-5 entry point

## Verdict (banked)
BOUNDED, kill-condition PASSES at EXACTLY ½·minAdm = ½·M0·M1 (Codex xhigh + rBlock·cBlock budget,
`codex/deeprank0-{prompt,answer}.md`). The deepRank=0 stratum (e.g. M=(1,1,2): unique tStar=![0,0])
is genuinely InteriorDrop, uncovered by the LIVE-leaf atom (its leafPivot needs 0<deepRank). Chart =
radial blow-up on the FRONT E-block (activeEImg.card = M0·M1 = minAdm at deepRank=0; leaf vacuous).

## DONE (sorry-free, green) — RouteMInteriorDeepRank0.lean @2e6352bd
1. `eBlockPivot` + `eBlockPivot_mem_activeM` (reuses activeSlotE_mem_activeM).
2-3. `eDeepRank0Phi := phiFlatLiveAt … eBlockPivot` + `eDeepRank0Phi_rate` (rate = (x p₀)²·V, reuses
   the PIVOT-GENERIC `phiFlatLiveAt_rate` verbatim — the rate half of routeMCore_interiorLivePhi
   transfers fully; leaf K-block untouched).
4. `eDeepRank0_leafH` (single-axis: minAdm−1 at pivot, 0 else) + `_pivot` (pure radial; all K-blocks
   vanish at deepRank=0, so NO LDU/Schur exponents).

## ITEM 5 — THE CRUX (det), entry point + the real shape
Goal: `|det D(eDeepRank0Phi) u| = ∏_j |u_j|^{eDeepRank0_leafH j} = |u eBlockPivot|^{minAdm−1}`.
Route: `radialComp_abs_det_at` (GENERIC in pivot, RouteMRadialComp:74) gives, given an hmap
`eDeepRank0Phi = B ∘ pivotBlowupOn activeM eBlockPivot` + `hasDB`:
   `|det Dφ| = |u eBlockPivot|^{minAdm−1} · |det DB|`.
Then need `|det DB| = 1` (pure radial, no boundary shear at deepRank=0) ⟹ single-axis monomial.

THE WALL (flagged, NOT thrashed): the existing hmap (`hmap_leaf`) → `chartParamsGen_match` →
`{Cgen1,Cgen2,Nblk,Wblk}_match` → `read{K,X,N,E,W}_pbo` are LEAF-BLOCK-STRUCTURED, not merely
leafPivot-indexed: `read*_pbo` are typed with leaf-block index types `Fin (Text (0+2)) = Fin(deepRank)`
(= Fin 0 at deepRank=0), `rfinFixedPivot` scales the LEAF block. The deepRank=0 chart INVERTS roles
(radial in FRONT E-block, leaf empty/spectator), so the hmap is NOT a leafPivot→p₀ substitution — it
needs a re-derived chart-parameter match for the E-radial decomposition:
   `chartParamsGen (x eBlockPivot) … (genBlkFlatLive … x) = (E-radial B-decoder) ∘ pbo_E`,
i.e. read*_pbo_E analogs (radial-in-E, leaf-spectator) + Cgen*_match_E. ~250-350 lines, real proof
work — the from-scratch chart-parameter-match (the ‖E·G‖² factorization surfacing in chart-param form).

Possible simplification to probe FIRST (could shrink item 5 a lot): at deepRank=0 the leaf block is
0-dim and genBlkFlatLive may reduce so that the residual map B (after the radial pivot) is LINEAR /
unimodular — if `|det DB| = 1` can be shown WITHOUT the full chartParamsGen_match (e.g. via a direct
phiGen-fderiv = pivotBlowup ∘ (measure-preserving reshape) argument, the RouteM4422 phi4422_abs_det
template: det = pb_abs_det · Q_abs_det with Q unimodular), item 5 collapses to the 4422-style
"radial · unimodular-reshape" det, avoiding the leaf-match machinery entirely. CHECK phiGen's fderiv
structure / whether chartParamsGen at deepRank=0 is affine-in-residual.

## TAIL (items 6-9, after item 5)
6. U a.e.-pos (VvalGen_ae_pos / all-ones template) + bounded-on-box + measurable.
7. injOn (mirror interiorLive_injOn with eBlockPivot in the inj domain).
8. cov + NodeAchieverChart₀ bundle + `routeMCore_box_diverges_eDeepRank0`.
9. wire into achiever_L2 interior branch (combine 0<deepRank atom + this → hInterior ∀ InteriorDrop).

## Bedrock reqs (lead, standing)
Pure-monomial pivotBlowupOn Jacobian throughout (NO poly-det fold — Item-102 trap); U-pos PROVED not
assumed; target axioms = [propext, Classical.choice, Quot.sound, monomial_rlct].
