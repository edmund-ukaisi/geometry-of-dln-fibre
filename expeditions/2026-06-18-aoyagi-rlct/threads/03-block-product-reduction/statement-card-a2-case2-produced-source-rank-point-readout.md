# Statement card - A2 Case 2 produced source-rank point readout

Status: Lean theorem added; focused build passed locally.

Reproduction:
`reproduction-a2-case2-produced-source-rank-point-readout.md`.

Review:
`review-a2-case2-produced-source-rank-point-readout.md`.

## Lean Declaration

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.

Theorem:

```text
exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
```

## Claim

For the endpoint-transported continuing Case 2 selected-entry chart, a center
value with nonzero selected pivot has a produced coordinate `yNext` such that
the associated retained-passive p.13 source edge family:

- lies in the fixed-base source-rank stratum;
- lies in the retained-passive p.13 local source;
- has fixed-base residual-coordinate map equal to the prescribed center value.

## Hypotheses

The theorem keeps the source-rank data explicit:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix
    ... (preimageOfPivotNeZero pivotNext value) ...) = rEdge 1.
```

It also assumes the existing continuing Case 2 endpoint-transport data and a
nonzero selected pivot value.

## Proof Inputs

The proof uses the same fixed-pivot selected-entry inverse as the existing
local-source/readout theorem, then combines:

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
```

The edge-1 rank hypothesis is pointwise at the produced inverse coordinate,
not uniform over all selected-entry coordinates.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

passed on 2026-06-29.

## Nonclaims

No source-rank coverage, selected-entry source/image equality, exact-rank
openness, successor-rank arithmetic, source-prior transport, Jacobian
compatibility, normal crossings, pole order, or RLCT is proved.
