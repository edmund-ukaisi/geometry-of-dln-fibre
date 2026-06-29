# Review - A2 retained-passive source-stratum membership

Date: 2026-06-29.

Reviewer: xhigh `Einstein the 2nd`.

Status: PASS.

## Findings

No findings.

## Checks

The reviewer checked:

- `ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C`;
- `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_edgeMatrix_rank`;
- `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank`;
- `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq`;
- `PaperEndpointFixedBaseRegularCoordinateSourceData.case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum`.

Endpoint transport only reindexes `C` by equivalences, and rank preservation is
by `Matrix.rank_submatrix`.

The source-rank stratum constructor supplies the base product rank by `hprod`,
derives the exact continuous-linear edge ranks from the fixed-base realised
edge matrices, and passes `hle` directly.  The residual-block variants derive
edge ranks only through the determinant-chart edge-rank formula and explicit
arithmetic hypotheses.

The Case 2 wrapper keeps the two intended edge ranks as assumptions:

```text
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix ...) = rEdge 1.
```

The successor selected-entry matrix rank remains a rank expression, not a
claimed fixed number.

## Verification

The reviewer ran:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

It passed.  Controller builds and hygiene are recorded in `synthesis.md`.

## Boundary

The slice is conditional and pointwise.  It does not prove local source-rank
coverage, exact-rank openness, selected-entry image equality, source-prior or
Jacobian transport, analytic atlas construction, normal crossings, pole order,
or RLCT.
