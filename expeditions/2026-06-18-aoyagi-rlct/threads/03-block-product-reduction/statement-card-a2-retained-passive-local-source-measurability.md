# Statement Card - A2 Retained-Passive Local-Source Measurability

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous
```

## Claim

If the source edge family `Cedge` is globally continuous, then the fixed-base
edge-matrix map into retained-passive source-family coordinates is continuous,
and the retained-passive p.13 local source is measurable.

## Proved

- global continuity of the fixed-base edge-matrix map from global continuity
  of `Cedge`;
- measurability of `paperEndpointFixedBaseRetainedPassiveP13LocalSource` as
  the preimage of the open set `sourceRecursiveDetChartSet`.

## Assumed

- finite-dimensional fixed-base endpoint data;
- global continuity `Continuous Cedge`;
- `OpensMeasurableSpace alpha`.

## Cited

None.  This is a topological/measurability bridge.

## Deferred

Residual integrability, loss comparison, density bounds, measure pushforward,
Jacobian density transport, bounded transported prior, normal crossings, pole
order, and RLCT extraction.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
```

Status at creation: focused build passed.  Xhigh review passed after
documentation correction; see
`review-a2-retained-passive-local-source-measurability.md`.
