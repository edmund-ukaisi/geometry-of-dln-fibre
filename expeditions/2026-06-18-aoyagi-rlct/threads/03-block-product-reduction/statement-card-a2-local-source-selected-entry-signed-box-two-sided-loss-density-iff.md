# Statement Card - A2 local-source selected-entry signed-box two-sided loss-density iff

Date: 2026-06-29.

## Claim

For a supplied local source represented by a selected-entry weighted signed-box
chart, the selected-entry monomial unit calculation and residual readout supply
the residual monomial lower bound needed for the local-source signed-box
two-sided p.13 loss-density iff.  With explicit residual local boundedness and
four supplied two-sided p.13 loss/density bounds, there is an open
neighborhood `U` such that actual p.13 loss-density integrability over

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
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

## Proved

- The selected-entry residual unit calculation gives the required monomial
  lower bound with constant `1`.
- The supplied residual readout transports this lower bound to the actual
  Aoyagi residual square-sum along `sourceChart`.
- The local-source signed-box two-sided theorem then gives the local
  loss-density finiteness iff.

## Assumed

- `MeasurableSet source`.
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`.
- Measurable fixed-basis edge matrices.
- The selected-entry source-chart a.e. measurability and weighted signed-box
  pushforward identity for `mu.restrict source`.
- The selected-entry residual readout.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on
  `mu.restrict source`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied local-source-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No p.13 chart construction or coverage theorem, no selected-entry critical
integrability proof, no source-prior/Jacobian or density transport, no
product-measure transport theorem, no original-loss identification, no normal
crossings, no pole order, and no RLCT extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`, touched
Lean-file forbidden-marker scan, direct axiom probe, and Boole xhigh
read-only review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
