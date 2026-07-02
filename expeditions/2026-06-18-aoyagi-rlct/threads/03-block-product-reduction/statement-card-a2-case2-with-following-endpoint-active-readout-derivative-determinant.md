# Statement card - A2 Case 2 with-following endpoint active-readout derivative determinant

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointDerivative.lean
```

Names:

```text
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv
Case2PassiveThetaWithFollowingFactor.hasFDerivAt_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv_absDet_eq_sourceDensity
Case2PassiveThetaWithFollowingFactor.fderiv_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.fderiv_endpointTopologyTupleActiveReadout_comp_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_absDet_eq_sourceDensity
```

## Claim

The source-type active selected-entry chart map

```text
((passive, yNext), following)
  |->
((passive, chartMap pivotNext yNext), following)
```

has Frechet derivative equal to the product map that is identity on passive
fields and the following factor and is the selected-entry chart derivative on
`yNext`.  The absolute determinant of this derivative is

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext yNext.
```

After composing the enlarged endpoint topology-tuple map `Y` with
`endpointTopologyTupleActiveReadout`, the same derivative determinant equality
holds pointwise.

## Inputs

- finite source index types `ρ`, `τ`;
- `[DecidableEq ρ]` for the endpoint active readout theorem;
- target tuple index family `κ'`;
- Case 2 bounds `hS`, `hcont`, and `hnext`;
- endpoint reindexing equivalences `eNext` and `e`;
- a source point `z`.

There is no source set, no radii, no measurability hypothesis, and no
selected-pivot-nonzero hypothesis in this determinant equality.
The following factor is the normalized retained/raw `C(0)` coordinate in this
Lean source model.

## Output

The endpoint-facing theorem states:

```text
let Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e
let R =
  endpointTopologyTupleActiveReadout n e
|det (fderiv R (Y .) at z)| =
  SelectedEntrySignedBox.CenterCoord.sourceDensity
    (case2PassiveThetaPivotNext n hS hnext) z.1.yNext
```

in Lean's precise syntax as the determinant of
`fderiv ℝ (fun z => R (Y z)) z` after coercion to a linear endomorphism.

## Dependencies

- `endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart`;
- `SelectedEntrySignedBox.CenterCoord.hasFDerivAt_chartMap`;
- `SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det`;
- `linearMap_det_prodMap_eq_mul`;
- `LinearMap.det_id`.

## Nonclaims

This is not a theorem about `det (fderiv Y)`: the bare endpoint map has a
different target type.  This is not a local change-of-variables theorem, not an
endpoint Haar/reference-image identification, not determinant-chart Haar
equality, not raw-Haar transport, not source-image coverage, not formal-product
domination, not normal crossings, not pole order, and not RLCT extraction.
