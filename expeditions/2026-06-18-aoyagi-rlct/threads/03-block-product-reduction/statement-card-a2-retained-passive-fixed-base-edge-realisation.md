# Statement card - A2 retained-passive fixed-base edge realisation

## Claim

For any retained-passive coordinate datum on the fixed-base endpoint complement
indices, the continuous reversed edge family realised from `data.edgeMatrix`
has fixed-base edge matrices exactly `data.edgeMatrix`.  If `data` lies in the
retained-passive determinant chart, source readback of that realised fixed-base
edge family recovers `data`.

## Lean artifacts

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`

Theorems:

```lean
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix

sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq
```

## Proved inputs

- `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`
  recovers any prescribed fixed-base matrix family.
- `sourceReadback_edgeMatrix_eq` recovers retained-passive data from its own
  `edgeMatrix` under `detChart`.

## Supplied inputs

- fixed-base endpoint data `W,B,U0,hU0`;
- a retained-passive datum `data`;
- `data.detChart` for the source-readback equality.

## Nonclaims

No retained-passive datum is constructed.  No Case 2 endpoint alignment is
proved.  No source chart image theorem, rank-stratum coverage, measure
pushforward, Jacobian/source-density theorem, original-loss comparison, normal
crossings, pole order, or RLCT extraction is proved.
