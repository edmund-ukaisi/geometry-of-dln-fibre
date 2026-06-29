# Statement card - A2 Case 2 residual-coordinate measure pushforward

Status: Lean theorem added; focused build passed locally.

Reproduction:
`reproduction-a2-case2-residual-coordinate-measure-pushforward.md`.

Review:
`review-a2-case2-residual-coordinate-measure-pushforward.md`.

## Lean Declarations

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.

Main theorem:

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_eq_restrict_chartMap_image
```

## Claim

For the endpoint-transported continuing Case 2 chart, let

```text
sourceMeasure =
  (signed selected-entry box measure).withDensity sourceDensity
mu = Measure.map sourceChart sourceMeasure
```

and let `residualMap` be the fixed-base residual-coordinate map reindexed by
`residualCoordEquiv.symm`.  Then

```text
Measure.map residualMap mu
= volume.restrict
    (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
      SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres).
```

The proof identifies `residualMap (sourceChart yNext)` pointwise with
`SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext` and applies the
existing finite selected-entry weighted pushforward theorem.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

passed on 2026-06-29, with only pre-existing upstream linter warnings in
`ProductReductionStepRegularDensity.lean`.

## Nonclaims

No external/original source-prior transport, source-rank coverage,
source/image equality, analytic Jacobian compatibility, normal crossings, pole
order, or RLCT is proved.  The theorem is about the chart-produced measure.
