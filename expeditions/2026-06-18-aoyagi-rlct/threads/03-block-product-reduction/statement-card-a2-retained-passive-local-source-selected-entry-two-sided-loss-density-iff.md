# Statement Card - A2 retained-passive local-source selected-entry two-sided loss-density iff

Date: 2026-06-29.

## Claim

For the retained-passive p.13 local source, continuity of the edge-family
parameter supplies the local-source measurability and fixed-basis edge-matrix
measurability needed by the selected-entry local-source two-sided
loss-density iff.  With an explicit selected-entry weighted signed-box
pushforward, residual readout, residual local boundedness, and four supplied
two-sided p.13 loss/density bounds, there is an open neighborhood `U` such
that actual loss-density integrability over

```text
(mu.restrict (U inter localSource)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
retained-passive local source:

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
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

## Proved

- The retained-passive local source is measurable under `Continuous Cedge`.
- The fixed-basis edge-matrix readout is measurable under `Continuous Cedge`.
- The selected-entry local-source two-sided iff applies with
  `source := localSource`.

## Assumed

- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- The selected-entry source-chart a.e. measurability and weighted signed-box
  pushforward identity for `mu.restrict localSource`.
- The selected-entry residual readout.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on
  `mu.restrict localSource`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied local-source-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No signed-box chart construction or pushforward proof, no selected-entry
critical-integrability proof, no retained-passive source coverage, no
source-rank coverage, no source-prior/Jacobian or density transport, no
product-measure transport theorem, no original-loss identification, no normal
crossings, no pole order, and no RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`, touched
Lean-file forbidden-marker scan, direct axiom probe, and Halley the 2nd xhigh
read-only review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
