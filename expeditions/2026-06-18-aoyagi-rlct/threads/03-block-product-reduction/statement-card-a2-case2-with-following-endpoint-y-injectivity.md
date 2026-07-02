# Statement card - A2 Case 2 with-following endpoint Y injectivity

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

Name:

```text
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
```

## Claim

The enlarged Case 2 endpoint topology-tuple map `Y` is injective on the locus
where the successor selected pivot coordinate is nonzero:

```text
Set.InjOn
  (fun z =>
    case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
      n hS hcont hnext z eNext e)
  {z | case2PassiveThetaPivotNonzero n hS hnext z.1}
```

Consequently, under the standard Lusin-Souslin hypotheses, every measurable
source subset `Ω` contained in that locus has measurable endpoint sector image
`Y '' Ω`.

## Inputs

- source and target index types `ρ`, `τ`, and `κ'`;
- `[DecidableEq ρ]`;
- Case 2 bounds `hS`, `hcont`, and `hnext`;
- endpoint reindexing equivalences `eNext` and `e`.
- for the measurable-image theorem: `MeasurableSpace`, `OpensMeasurableSpace`,
  `BorelSpace`, and `PolishSpace` on the source coordinate type, plus
  `MeasurableSpace`, `OpensMeasurableSpace`, and `T2Space` on the endpoint
  topology-tuple target;
- a measurable source set `Ω` with
  `Ω ⊆ {z | case2PassiveThetaPivotNonzero n hS hnext z.1}`.

## Output

If `z` and `w` lie in the selected-pivot-nonzero locus and their endpoint
topology tuples agree, then `z = w`.

If `Ω` is a measurable subset of the selected-pivot-nonzero locus, then

```text
MeasurableSet
  (case2PassiveThetaWithFollowingFactorEndpointSectorSet
    n hS hcont hnext eNext e Ω)
```
holds.

## Dependencies

- `endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart`;
- `SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero`;
- `case2PassiveThetaPivotNonzero`;
- `continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`;
- `MeasurableSet.image_of_continuousOn_injOn`;
- product and structure extensionality for `Case2PassiveThetaWithFollowingFactor`.

## Nonclaims

No local change-of-variables formula, no Jacobian determinant theorem, no
determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond actual images, no formal-product
domination, no normal crossings, no pole order, and no RLCT extraction.
