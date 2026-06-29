# Statement Card - A2 retained-passive chart-produced selected-entry two-sided loss-density iff

Date: 2026-06-29.

## Claim

For the chart-produced measure

```text
mu = Measure.map sourceChart
  ((signedBox).withDensity selectedEntrySourceDensity),
```

pointwise landing of `sourceChart` in the retained-passive p.13 local source
derives the local-source restriction equality required by the retained-passive
local-source selected-entry two-sided iff.  With explicit residual readout,
residual local boundedness, and four supplied two-sided p.13 loss/density
bounds, there is an open neighborhood `U` such that actual loss-density
integrability over

```text
(mu.restrict (U inter localSource)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
local source:

```text
residualNegPowerIntegrableOn Cedge (U inter localSource) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

## Proved

- The chart-produced measure restricts to the retained-passive local source
  when the chart lands there pointwise.
- The retained-passive local-source selected-entry two-sided iff applies with
  `mu = Measure.map sourceChart sourceMeasure`.

## Assumed

- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- The selected-entry source-chart a.e. measurability for the unweighted signed
  box.
- Pointwise chart landing in the retained-passive local source.
- The selected-entry residual readout.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on the
  chart-produced measure restricted to `localSource`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied local-source-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No proof of chart landing, residual readout, comparison bounds, or residual
boundedness; no selected-entry critical-integrability proof; no retained-
passive source coverage; no source-rank coverage; no source-prior/Jacobian or
density transport beyond the chart-produced restriction equality; no original-
loss identification; no normal crossings, pole order, or RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`, touched
Lean-file forbidden-marker scan, direct axiom probe, and Carver the 2nd xhigh
read-only review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
