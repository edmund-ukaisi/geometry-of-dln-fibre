# Review - A2 retained-passive p.13 named source chart

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Galileo the 4th`.

## Scope

Audit the named fixed-base retained-passive p.13 source-chart layer in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean` and the associated
reproduction and statement-card notes.

Reviewed Lean artifacts:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceChart_eq
sourceReadback_paperEndpointFixedBaseRetainedPassiveP13SourceChart_eq
paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_localSource
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
```

## Verdict

PASS.  No blocking findings.

## Checks

The change stays inside the Aoyagi-side Lean development and introduces no
quiver-paper, measure, Jacobian, normal-crossing, pole-order, or RLCT
dependency.

The theorem names match their statements:

- edge-matrix extraction only;
- source readback only;
- pointwise local-source membership only;
- continuity of the named coordinate-to-source edge-family map only.

The named map is thin but not vacuous: it packages the concrete
determinant-chart source edge family used when the fixed-base edge matrices
are realised directly from `data.edgeMatrix`, and it provides the API facts
needed for downstream retained-passive source-chart work.

The proof shape is stable because it composes existing prescribed-matrix
realisation, retained-passive readback, determinant-chart membership, and
continuity lemmas.

## Advisory

The term `SourceChart` can sound stronger than the theorem content if read in
isolation.  The definition docstring and the statement card should continue to
state that this is the coordinate-to-source edge-family leg, not a source-image
equality, local inverse for arbitrary source points, source-rank coverage,
measure pushforward, density/Jacobian theorem, normal-crossing theorem, pole
order, or RLCT extraction.
