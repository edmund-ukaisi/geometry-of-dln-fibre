# Codex consult — the radical ideal-split: tractable, or needs absent machinery? (Lean v4.29)

Greenlit to grind the make-or-break radical ideal-split (route (c), thread 31). I need a sharp
read on tractability BEFORE sinking the module budget, and which ring the normalizing gauge lives
over. STOP→fallback (cite `hSweep`) is authorized if it needs a Mathlib-absent sub-theorem.

## The architecture (LANDED in the engine)

- `ΔPdeep` = the top-left r×r minor of `of (multPoly d)` (the TOTAL-ring pivot minor), in
  `MvPolynomial (RepCoord d) k`.
- `Sred = Localization.Away ΔPdeep ⧸ IadDeep`, where `IadDeep = (sigmaIdeal d r).map (algebraMap
  (MvPolynomial (RepCoord d) k) (Localization.Away ΔPdeep))`. `sigmaIdeal` = vanishing ideal of the
  rank-≤r product locus Σ̄^r (radical, alg-closed).
- `SchurLoc = Localization.Away detSchurS` (the BASE chart ring, a localized polynomial ring in δ
  vars, `dim = δ`). `basePresentationEquiv : Localization.Away detPivotPoly ⧸ Iad ≃ₐ[k] SchurLoc`.
- `baseLocMap : Localization.Away detPivotPoly →ₐ[k] Localization.Away ΔPdeep` (the base→total
  localized ring map, `IsLocalization.Away.mapₐ deepBaseComap`).
- `schurToSred : SchurLoc →ₐ[k] Sred` makes `Sred` a `SchurLoc`-algebra.
- I have LANDED `schurComplement_normal_form` (network-free): `L⁻¹·M·H⁻¹ = diag(I_r,0)` for
  `M = [[Δ,B12],[B21,B22]]`, `Δ` invertible, `B22 = B21 Δ⁻¹ B12`. And a gauge `gaugeEquiv` (an
  `AlgEquiv` of `MvPolynomial (RepCoord d) R`) for any coeff ring `R`, with `gaugeEquiv_multPoly`.

## The target (the split)

`ringKrullDim Sred = ringKrullDim SchurLoc + ringKrullDim FibreAlg = δ + ringKrullDim FibreAlg`,
where `FibreAlg = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`. Radical-level route:
`((gauge.map IadDeep).radical = splitBaseFibreIdeal.radical)`, then `Ideal.quotientEquivAlg` +
`ringKrullDim_quotient_eq_of_radical_eq` (LANDED) + the poly-extension dim.

## My ring confusion (resolve this first)

The normalizing gauge inverts the PIVOT minor. Two candidates for which ring it lives over:
(a) `SchurLoc` (the base — `detSchurS` is the base pivot), where I built my `endpointGauge`; or
(b) `Localization.Away ΔPdeep` (the total localization — `ΔPdeep` is the total pivot, which is the
    image of `detPivotPoly` under `deepBaseComap`).
`IadDeep` lives over (b). My `endpointGauge` is over (a). To gauge `IadDeep` I seemingly need the
gauge over (b), with blocks = images of the Schur blocks under `baseLocMap`. **Q1: is the gauge over
(b) the right object, and is it just `endpointGauge` transported along `baseLocMap`/`schurToSred`, or
do I rebuild it over (b) from `ΔPdeep`'s own pivot data?**

## The real questions

1. **Which ring for the gauge** (Q1 above) + the cleanest Lean shape to get a gauge that acts on
   `IadDeep`'s ambient ring `Localization.Away ΔPdeep`.
2. **Is the split `(gauge.map IadDeep).radical = splitBaseFibreIdeal.radical` tractable at v4.29, or
   does it need a Mathlib-absent sub-theorem?** Specifically the two containments:
   - `⊆`: the gauged `sigmaIdeal` generators (bordered (r+1)-minors of `multPoly`) become, after the
     Schur normalization, the "fibre" generators + the base δ-coordinate relations. Is this a finite
     explicit generator computation (tractable), or does it need a structural ideal-image theorem?
   - `⊇`: the harder direction (the R2-3b-4 wall was the forward map needing `sigmaIdeal ≤ ker`).
     At the RADICAL/dimension level, does `⊇` reduce to a height/dimension count (both ideals have
     the same height, both prime-ish → equal) that SIDESTEPS the explicit generator containment?
     I have `ringKrullDim_quotient_radical` (radical-insensitivity) landed.
3. **Is there a SHORTER dimension-only path** that avoids the explicit ideal-split entirely — e.g.:
   `Sred` is a `SchurLoc`-algebra (via `schurToSred`); if I can show `Sred` is module-finite or a
   localized-polynomial extension of `SchurLoc ⊗ (something dim 0)`... OR use that
   `Sred ≅ Localization.Away ΔPdeep ⧸ IadDeep` and compute `ringKrullDim` of the localized quotient
   directly via the LANDED determinantal/orbit dimension machinery (the engine already computes
   `dim Σ̄^r = card − C` and `dim Mat^{≤r} = δ`)? Could the chart dimension come from
   `dim Σ̄^r − dim(complement of chart)` or a localization-dim argument, WITHOUT building the split?
4. **Honest verdict**: is the radical ideal-split a ~2-3-module tractable grind, or is it the
   R2-3b-4 wall in disguise (needs the absent localized-quotient-interchange / structural ideal
   theorem)? If the latter, I STOP and cite `hSweep`. Be adversarial — I have a STOP→B authorization
   and would rather take a clean B than grind a wall.

Give me: the right gauge ring, the tractability verdict on each containment (or the height-count
sidestep), any shorter dimension-only path, and a clear "grind it (~N modules)" vs "STOP→B" call.
