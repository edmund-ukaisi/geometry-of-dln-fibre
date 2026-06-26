# Statement Card - A2 retained-passive p.13 named source chart

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceChart_eq
sourceReadback_paperEndpointFixedBaseRetainedPassiveP13SourceChart_eq
paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_localSource
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
```

## Reproduction

```text
reproduction-a2-retained-passive-p13-named-source-chart.md
```

## Claim

For a determinant-chart retained-passive coordinate datum `data`, the named
source chart

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U0 hU0 data
```

is the fixed-base continuous reverse-edge family realised from
`data.1.edgeMatrix`.  Fixed-base edge-matrix extraction recovers
`data.1.edgeMatrix`, source readback recovers `data.1`, and the point `data`
belongs to the fixed-base retained-passive p.13 local source for this named
chart.  The chart map is continuous on the determinant-chart subtype.

## Method

The edge-matrix identity specializes the prescribed-matrix realisation theorem
to `data.1.edgeMatrix`.  The source-readback identity then applies
`sourceReadback_edgeMatrix_eq` using `data.2 : data.1.detChart`.  Local-source
membership uses `sourceRecursiveDetChart_edgeMatrix_of_detChart`, again after
substituting the recovered fixed-base edge matrices.  Continuity composes
`continuous_edgeMatrix_detChart_subtype` with
`paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous`.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
```

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Both passed on 2026-06-26.  `scripts/sorries` reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`, and `git diff --check` passed.

Review:

```text
review-a2-retained-passive-p13-named-source-chart.md
```

## Nonclaims

This does not construct a local inverse from arbitrary source points, source
image equality, source-rank coverage, source-measure pushforward, density or
Jacobian accounting, selected-entry residual-factor compatibility, normal
crossings, pole order, or RLCT extraction.
