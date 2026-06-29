# Statement Card - A2 local-source signed-box two-sided loss-density iff

Date: 2026-06-29.

## Claim

For a supplied local source represented by a weighted signed-box residual chart,
monomial residual-positivity data plus explicit local boundedness and two-sided
p.13 loss/density bounds give an open neighborhood `U` such that actual p.13
loss-density integrability over

```text
(mu.restrict (U inter source)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source:

```text
residualNegPowerIntegrableOn Cedge (U inter source) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

## Proved

- Residual-square-sum `AEMeasurable` follows from measurable fixed-basis edge
  matrices.
- The positivity-only weighted signed-box monomial-lower helper supplies
  residual positivity a.e. on `mu.restrict source`.
- Under the explicit residual bound `residualSquareSum <= Rreg^2` and supplied
  two-sided loss/density bounds, Lean produces an open `U` with the actual
  loss-density finiteness iff the residual negative-power integral is finite on
  `U inter source`.

## Assumed

- `MeasurableSet source`.
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- The signed-box source-chart measurability and pushforward identity.
- The residual monomial lower bound with positive constant `cres`.
- The local residual boundedness `residualSquareSum <= Rreg^2` on
  `mu.restrict source`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied source-filter loss/density bounds.

## Cited

None in this theorem.  It uses only in-repo Aoyagi formalisation layers and
Mathlib measure-theory infrastructure.

## Deferred

No p.13 chart construction or coverage theorem, no source-prior/Jacobian or
density transport, no product-measure transport theorem, no original-loss
identification, no normal crossings, no pole order, and no RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`,
touched-file forbidden-marker scan, and direct axiom probes passed.  The axiom
footprint is `[propext, Classical.choice, Quot.sound]`.  Initial xhigh review
requested this positivity-only weakening; follow-up xhigh review passed.
