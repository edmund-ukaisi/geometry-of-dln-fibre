# Statement Card - A2 retained-passive source-stratum selected-entry two-sided loss-density iff

Date: 2026-06-29.

## Claim

For the retained-passive p.13 local source represented by a selected-entry
weighted signed-box chart, the selected-entry residual monomial lower bound
and supplied residual readout give residual positivity on the local source.
Using the retained-passive self-base local coverage theorem, residual
measurability, residual positivity, and explicit residual boundedness on the
local source transfer to a source-rank-stratum neighborhood.  With four
supplied two-sided p.13 loss/density bounds on the source-rank stratum, there
is an open neighborhood `U` such that actual loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source-rank stratum:

```text
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

## Proved

- Source-rank-stratum measurability under `Continuous Cedge`.
- Residual-square-sum measurability on the retained-passive local source.
- Residual positivity on the retained-passive local source from the
  selected-entry monomial lower bound and signed-box pushforward.
- Application of the retained-passive self-base local coverage theorem.
- Application of the source-stratum/local-source two-sided iff.

## Assumed

- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- `Continuous Cedge` and the self-base equation at `x0` needed by the
  retained-passive local coverage theorem.
- The selected-entry source-chart a.e. measurability and weighted signed-box
  pushforward identity for `mu.restrict localSource`.
- The selected-entry residual readout.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on
  `mu.restrict localSource`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied source-stratum-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No signed-box chart construction or pushforward proof, no residual-readout
proof, no selected-entry critical-integrability proof, no source-prior/Jacobian
or density transport, no product-measure transport theorem, no original-loss
identification, no normal crossings, no pole order, and no RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`, touched
Lean-file forbidden-marker scan, direct axiom probe, and Cicero the 2nd xhigh
read-only review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
