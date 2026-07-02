# Review - A2 Case 2 enlarged following-factor source-to-raw block Jacobian

Date: 2026-07-02.

Reviewer: Hooke, xhigh read-only sidecar audit.

Verdict: PASS, with a density-convention clarification.

## Findings

No blocking mathematical issue was found in the block-triangular determinant
claim for

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple z.
```

For `Y` before `topologyTupleEdgeRawOrder`, the expected absolute determinant
is

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext
```

up to endpoint/reindexing constants.  Under the current Lean product-coordinate
and finite endpoint-reindexing convention, those constants have absolute value
`1`.

The retained-passive factor

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
```

does not belong to `J_Y`; it enters only after composing with
`topologyTupleEdgeRawOrder`.

## Caveats

- The selected-pivot nonzero hypothesis is essential.  Without it, the
  selected-entry inverse/readback API fails, and the determinant may vanish.
- The determinant-sector hypotheses on `Ctop` and passive `A1passive` are
  still needed for the retained-passive bridge.
- The statement is for Lean's normalized following-factor convention.  The
  identity/reindexing `F -> raw C(0)` uses
  `case2DisplayedPostPivotFreeCprimeOfFollowingFactor` and
  `case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor`.
- Endpoint transports and matrix submatrix reindexings are finite coordinate
  permutations in the current model.  If a later theorem uses arbitrary Haar
  normalizations, carry a positive endpoint constant explicitly.
- Source-side weighted pushforward is the primary COV convention:

  ```text
  Measure.map Y ((sourceVolume.restrict V).withDensity (ofReal J_Y))
    = targetVolume.restrict (Y '' V).
  ```

  Relative to target Haar as the base measure, the unweighted source-image
  measure has inverse density `1 / J_Y(readback y)`.  Relative to the
  unweighted source-image measure `Measure.map Y (sourceVolume.restrict V)`,
  the target volume has forward density `J_Y(readback y)`.

## Lean Support

- `Case2PassiveThetaWithFollowingFactor`,
  `case2PassiveThetaWithFollowingFactorRetainedData`, and
  `case2PassiveThetaWithFollowingFactorEndpointTopologyTuple` in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean`.
- `case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor`
  in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.
- `case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor`
  in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`.
- `SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det`
  and
  `SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero`
  in `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`.
- The enlarged readback and raw-order/two-stage bridge in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean`.

## Next Theorem

Prefer a source-side weighted pushforward theorem for `Y` first.  A bounded
domination wrapper is useful downstream, but should be derived from the
source-side determinant theorem rather than replacing it.
