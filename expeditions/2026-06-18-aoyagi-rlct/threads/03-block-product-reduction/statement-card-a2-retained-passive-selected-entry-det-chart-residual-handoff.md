# Statement card - A2 retained-passive selected-entry determinant-chart residual handoff

## Declaration

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_map
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Statement

For the retained-passive p.13 determinant chart, suppose a selected-entry
signed-box map

```text
chart : (center -> R) -> TopologyTuple rho kappa' R
```

is a.e. measurable on the signed box and satisfies the pushforward identity

```text
m.restrict topologyTupleDetChartSet =
  Measure.map chart
    (signedBox.withDensity
      (fun y => ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))).
```

Assume also that the determinant-chart residual positive set is measurable and
that the residual readout holds pointwise:

```text
residualSquareSum (directChart (chart y)) =
  SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

Under positive signed-box radii, `0 <= t`, and

```text
2 * t < ((center.erase pivot.1).card : R) + 1,
```

the determinant-chart residual is positive for `m.restrict
topologyTupleDetChartSet`-almost every point and has finite negative-power
lower integral over that restricted measure.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 determinant/source
coordinates and pp. 19-22 for the selected-entry chart shape.  The analytic
calculation used here is the already formalised selected-entry weighted-box
residual theorem:

```text
SelectedEntrySignedBox.CenterCoord.
  residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
```

The new theorem only transports that calculation through a supplied
pushforward equality and a supplied residual readout using `ae_map_iff` and
`lintegral_map_le`.

## Boundary

This does not construct the selected-entry determinant-chart map, prove chart
coverage, prove the determinant-chart pushforward identity, identify an
original external DLN prior, prove local loss or density bounds, prove
source-rank coverage, construct normal crossings, compute a pole order, or
extract an RLCT.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched-file forbidden-marker
search, direct axiom probe, and xhigh review.

## Verification Result

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker search, and direct
axiom probe passed; the new declaration reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only review by Parfit
passed.
