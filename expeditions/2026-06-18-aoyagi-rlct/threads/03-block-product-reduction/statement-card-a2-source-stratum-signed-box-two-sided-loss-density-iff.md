# Statement Card - A2 source-stratum signed-box two-sided loss-density iff

Date: 2026-06-29.

## Claim

For Aoyagi's source-rank stratum, a supplied weighted signed-box residual chart
with residual monomial positivity data, explicit residual local boundedness,
and supplied two-sided p.13 loss/density bounds gives an open neighborhood `U`
such that actual p.13 loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source stratum:

```text
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

## Proved

- The local-source signed-box two-sided theorem specialises to
  `paperEndpointFixedBaseSourceRankStratum`.
- The resulting open set `U` gives actual loss-density finiteness iff residual
  negative-power integrability on `U inter sourceStratum`.

## Assumed

- `MeasurableSet sourceStratum`.
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- Measurable fixed-basis edge matrices.
- The signed-box source-chart measurability and source-stratum pushforward
  identity.
- Residual monomial lower bound with positive constant `cres`.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on
  `mu.restrict sourceStratum`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied source-stratum-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No p.13 chart construction or coverage theorem, no source-prior/Jacobian or
density transport, no product-measure transport theorem, no original-loss
identification, no signed-box critical-integrability proof, no normal
crossings, no pole order, and no RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`,
touched-file forbidden-marker scan, and direct axiom probe passed.  The axiom
footprint is `[propext, Classical.choice, Quot.sound]`.  Anscombe xhigh
read-only review passed.
