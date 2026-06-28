# Statement card - A2 Case 2 endpoint-transport source-edge-family residual square-sum

## Claim

For the two-edge Case 2 endpoint-transport source chart, the fixed-base
residual-block coordinate square-sum equals the successor selected-entry center
residual.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Proof Basis

Use the endpoint-transport source-family pre-measure wrapper to obtain the
source-readback residual-factor selected-entry matrix identity, then apply the
generic fixed-base residual-square-sum readout bridge at `M := 1`.

## Nonclaims

This theorem does not construct endpoint equivalences, prove source-chart
measurability, compare source priors or Jacobians, prove positivity or
integrability, produce normal crossings, compute pole order, or extract RLCT.

## Status

Sorry-free, focused build passed, and reviewed PASS by xhigh `Einstein` in
`review-a2-case2-endpoint-transport-source-edge-family-residual-square-sum.md`.
