# A2 retained-passive topology-tuple punctured-sector transport

## Scope

This note reproduces a narrow topology/source-chart packaging step for the
with-passive Case 2 selected-entry sector.  It is not a new Aoyagi source
calculation.  Aoyagi pp. 10-13 supply the retained-passive p.13 block/product
coordinates, and the existing Case 2 selected-entry notes supply the residual
chart calculation.  The present step records how the repo-local topology tuple
and raw-order chart infrastructure presents the same chart-produced source
edge family on the punctured sector.

## Objects

For a point

```text
z : eta x (center -> R),
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
```

define the endpoint-transported retained-passive datum

```text
data z =
  (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    n hS hcont hnext
    (A1passive z.1) (F2 z.1) (A3passive z.1)
    (Ctop z.1) (F3 z.1) z.2 eNext).endpointTransport e.
```

The chart-produced source family is

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (data z).
```

The topology-tuple presentation of the same datum is

```text
y z   = topologyTuple (data z),
raw z = topologyTupleEdgeRawOrder (y z).
```

The selected-entry inverse readout used on source edge families is

```text
inverseReadout X =
  preimageOfPivotNeZero pivotNext
    (fun i =>
      paperEndpointFixedBaseResidualBlockCoordinateMap
        W2 B2 U0 hU0 id X (residualCoordEquiv.symm i)).
```

## Determinant and raw-order chart calculation

On the determinant chart, the raw-order map has the expected inverse:

```text
topologyTupleEdgeRawOrderInverse
  (topologyTupleEdgeRawOrder (topologyTuple data))
= topologyTuple data.
```

Also `ofTopologyTuple (topologyTuple data) = data`.  Therefore the raw-order
p.13 source chart, which first inverts raw order and then reads the retained
edge matrices, agrees with the direct fixed-base source edge family:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart (raw z)
= sourceChart z.
```

The needed determinant-chart hypothesis for `data z` is obtained on the open
sector from the existing source-readback theorem: `sourceChart z` lies in the
retained-passive p.13 local source, so its extracted edge matrix lies in
`sourceRecursiveDetChartSet`; source readback recovers `data z`; and
`sourceReadback_detChart_of_sourceRecursiveDetChart` then gives
`(data z).detChart`.

Consequently

```text
y z in topologyTupleDetChartSet,
raw z in topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The second membership is exactly the maps-to property of
`topologyTupleEdgeRawOrder` on the determinant chart.

## Punctured residual readout

The already proved open source-readback theorem gives, on a determinant-domain
neighborhood,

```text
sourceReadback(edgeMatrix(sourceChart z)) = data z
```

and the Case 2 selected-entry residual factor calculation gives

```text
paperEndpointFixedBaseResidualBlockCoordinateMap (sourceChart z)
= chartMap pivotNext z.2
```

after reindexing residual coordinates by `residualCoordEquiv`.

On the punctured sector

```text
z.2 pivotNext != 0,
```

the selected-entry inverse identity applies:

```text
preimageOfPivotNeZero pivotNext (chartMap pivotNext z.2) = z.2.
```

Thus

```text
inverseReadout (sourceChart z) = z.2.
```

## Open sector

The theorem takes the open determinant-domain neighborhood returned by the
existing readback theorem and intersects it with the open pivot-nonzero set

```text
{z | z.2 pivotNext != 0}.
```

The basepoint belongs to this sector by the explicit hypothesis
`z0.2 pivotNext != 0`.

## Kill conditions

- Kill if the theorem claims Aoyagi states the repo-local topology tuple or
  raw-order chart infrastructure.
- Kill if inverse readout is claimed without the selected-pivot nonzero
  condition.
- Kill if determinant-chart or raw-order membership is asserted without a
  determinant-chart witness for the retained datum.
- Kill if endpoint equivalences are described as canonical or label-preserving
  provenance rather than supplied transport data.
- Kill if the result is described as a measure pushforward theorem,
  determinant-chart Haar transport, raw/source Haar theorem, external/original
  source-prior comparison, source-image equality, source-rank coverage, normal
  crossings, pole order, or RLCT.

## Formalisation target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
```

Target name:

```text
exists_open_case2EndpointTransport_withPassive_topologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq
```

The statement should return an open `V` containing `z0` such that for every
`z in V`, the topology tuple lies in the determinant chart, its raw-order
image lies in the raw-order source-recursive determinant chart, the raw-order
p.13 source chart equals `sourceChart z`, source readback recovers
`retainedData z`, and `inverseReadout (sourceChart z) = z.2`.
