# Statement Card - A2 retained-passive tuple source map

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTuple_ofTopologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple_topologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleDetChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleEdgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.mapsTo_topologyTupleEdgeMatrix_detChartSet_sourceRecursiveDetChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.injOn_topologyTupleEdgeMatrix_detChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.image_topologyTupleEdgeMatrix_detChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_ofTopologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.isOpen_topologyTupleDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-tuple-measure-jacobian-plan.md
```

## Claim

The retained-passive nonredundant coordinate record has an explicit product
tuple reconstruction.  In tuple coordinates, the fixed-base source map

```text
z |-> (ofTopologyTuple z).edgeMatrix
```

maps the tuple determinant chart into the source-recursive determinant chart,
is injective on that tuple determinant chart, and has image exactly the
source-recursive determinant chart.  The tuple determinant chart is open.

## Method

The tuple reconstruction is by field projection from the nested product
tuple.  The source-map facts are direct translations of the existing
record-level inverse theorems:

```text
sourceRecursiveDetChart_edgeMatrix_of_detChart
edgeMatrix_ext_of_detChart
edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
sourceReadback_detChart_of_sourceRecursiveDetChart
```

The openness theorem uses the induced product topology on the record: the
tuple reconstruction is continuous because `topologyTuple (ofTopologyTuple z)`
is definitionally `z`, and the record determinant chart was already open.

## Role

This is the first retained-passive tuple-coordinate API needed for a future
derivative/Jacobian package.  It gives the source map as an ambient finite
tuple map and gives its determinant-domain set in tuple coordinates.

## Nonclaims

No Frechet derivative, Jacobian determinant formula, inverse density, measure
pushforward, source-rank coverage, original DLN source-measure theorem, normal
crossings, pole order, or RLCT extraction is proved.

## Verification

Focused check passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```
