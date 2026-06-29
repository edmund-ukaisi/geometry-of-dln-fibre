# Affine-radial verdict: resolved on the CONCRETE banked (2,2,2) — pure-multiplicative radial, NO anchor

## The question
For the DLN interior-det headline, route (i): does the achiever chart factor as φ = B ∘ (radial), with
B a u-free LOCAL ISO (det = engine ≠ 0) and the radial det = u^{minAdm−1}? Prior worry: the gauge-fixed
pivot's "u·1 anchor" needs an AFFINE radial layer (additive u·1 at the anchor), which might break things.

## What I found on the CONCRETE banked decoder (not a toy model)
The (2,2,2) achiever chart is BANKED as `T222 = bsubst222 ∘ shear222 ∘ pb222`, with `chartParams222 =
pack222 ∘ T222` and `phi222_abs_det = |u0|²·|u4|` (all sorry-free in the repo):
- `pb222 = pivotBlowupOn {0,6,7} 0` — the RADIAL, PURE-MULTIPLICATIVE (x_i ↦ x_p·x_i on actives), det u0²
  = u^{minAdm−1} (minAdm=3, active card 3). NO affine term.
- `shear222` — det-1 unitriangular Schur shear.
- `bsubst222 = pivotBlowupOn {1,4} 4` — boundary/spectator, det u4 = the engine |K|.
- B := pack222 ∘ bsubst222 ∘ shear222 is u-FREE (in the pivot) and a LOCAL ISO: det D(bsubst∘shear) = u4 ≠ 0.

So φ = (paramsEquivFlat ∘ pack222 ∘ bsubst222 ∘ shear222) ∘ pb222 — pure-multiplicative radial + u-free
local-iso B, det u0²·u4 = u^{minAdm−1}·engine. EXISTS + BANKED. NO affine radial layer needed.

## The conflation I was making (and want you to sanity-check)
My earlier dead-ends (hslot false, hchart undischargeable, "u·1 additive anchor") ALL came from misreading
`genBlkFlatLiveR1`'s `Rmat p = u·pivotEIndicator` (a literal-1 E-block scaled by u) as an ADDITIVE `u·1`
CONSTANT in the chart output. But in the actual COMPOSITE chart, the pivotEIndicator's structural `1`
combines into the radial COORDINATE direction (the pivot coord u0) that pb222 blows up MULTIPLICATIVELY —
it is NOT an additive constant. The `pack`/`T`-reshape route (the banked (2,2,2) template) is the RIGHT
decomposition; my `RouteMBData` route (B = phiGen 1 (genBlkFlatLiveR1) + smulRmatRfin, with the false hslot)
was the wrong decomposition — a different, non-realizable B.

## Questions
1. Is my reading correct: the achiever chart's radial direction is the pivot COORDINATE (blown up
   multiplicatively by `pivotBlowupOn`), NOT an additive `u·1`, so NO affine radial layer is needed, and
   the realizable u-free local-iso B exists (the `pack ∘ bsubst ∘ shear` reshape)?
2. The general-M route is then: generalize the (2,2,2) `T = (boundary blow-ups/Schur frames) ∘ shears ∘
   (radial blow-up)` + `pack`-reshape `composeFold` decomposition. This IS the engine-factor composeFold
   route (bsubst/schur = boundary, shear = det-1 chain) — but realized as ACTUAL MAPS (the pack/T reshape),
   which the a8427f verdict said is BOUNDED via route (i). Confirm: is the `pack`/`T`/`pb` map-composition
   the faithful realizable form (vs my failed B = phiGen 1(genBlkFlatLiveR1))? 
3. Any reason the (2,2,2) pure-multiplicative-radial decomposition does NOT generalize to L=2 ∀M / general
   M (e.g. multi-dim K-core where the "radial = single pivot coord" might fail)? At (2,2,2) the K-core is
   1×1 so bsubst is a scalar blow-up; at general M the boundary is a Schur frame (schurFrameMap). Does the
   radial stay a pure pivotBlowupOn (the structPivot coord) regardless?

Be concrete + skeptical. Confirm the pure-multiplicative-radial resolution (no affine) or find the hole.
