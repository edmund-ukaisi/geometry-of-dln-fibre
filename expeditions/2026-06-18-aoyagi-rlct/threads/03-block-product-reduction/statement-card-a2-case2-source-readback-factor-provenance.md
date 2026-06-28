# Statement Card - A2 Case 2 source-readback factor provenance

## Claim

For the fixed-base p.13 source edge family built from the endpoint-transported
explicit Case 2 selected-entry retained-passive datum, `sourceReadback`
recovers that datum.  Consequently, the readback's adjacent factors `C 1` and
`C 0`, submatrixed by the forward endpoint equivalences, are the displayed
post-pivot residual block and displayed free following factor.

## Source / Proof Basis

Aoyagi PDF pp. 19-22 for the Case 2 displayed post-pivot residual and
following-factor construction; Lean fixed-base retained-passive source/readback
inverse for the p.13 source chart.

Lean dependencies:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
sourceReadback_edgeMatrix_eq
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Expected declarations:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_one_submatrix_eq_displayedPostPivotResidualBlock_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Nonclaims

No construction of `tau`, no proof of `hTau`, no label-preserving endpoint
provenance, no arbitrary `ofTopologyTuple` factor alignment, no source-prior
transport, no Jacobian comparison, no normal crossings, no pole order, and no
RLCT.

The endpoint equivalences `eNext` and `e` remain supplied.

## Verification Plan

Run a focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probes for the new declarations, and xhigh implementation review.
