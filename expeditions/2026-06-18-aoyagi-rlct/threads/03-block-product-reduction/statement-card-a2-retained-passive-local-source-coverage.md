# Statement Card - A2 Retained-Passive Local-Source Coverage

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean
```

## Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
```

## Claim

Near a self-base continuous edge family, the retained-passive p.13 local source
defined as the fixed-base edge-matrix preimage of
`sourceRecursiveDetChartSet` is a neighborhood of the base parameter.  Hence
there exists an open `Ulocal` containing the base parameter such that
`Ulocal` is contained in this chart-tied local source, and therefore

```text
Ulocal inter paperEndpointFixedBaseSourceRankStratum ... subset
  Ulocal inter paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

## Proved

- the chart-tied retained-passive local source definition;
- equivalence between its membership and
  `paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts`;
- local neighborhood membership at a self-base continuous edge family;
- the open-neighborhood inclusion needed as the `hcoverage` shape for the
  local-measure consumer.

## Assumed

- a fixed base chain `B`;
- a complement `U0` with `hU0 : IsCompl U0 (ker (paperTotalMap W B))`;
- a continuous edge family `Cedge`;
- the self-base condition
  `Cedge x0 = fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)`.

## Cited

None.  This is a finite/topological determinant-chart bridge.  The expedition's
normal-crossing-to-RLCT extraction remains a separate cited analytic boundary.

## Deferred

Exact-rank openness, global source-rank finite cover, source-image equality,
measurability of the retained-passive local source, measure pushforward,
Jacobian density transport, bounded transported prior, normal crossings, pole
order, and RLCT extraction.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
```

Status at creation: focused build passed.  Xhigh review passed after wording
correction; see `review-a2-retained-passive-local-source-coverage.md`.
