# Statement Card - A2 Case 2 passive theta relative raw-order endpoint sector

Status: proved in Lean and independently reviewed.

Reproduction:

```text
reproduction-a2-case2-passive-theta-relative-raw-order-endpoint-sector.md
```

Review:

```text
review-a2-case2-passive-theta-relative-raw-order-endpoint-sector.md
```

## Claim

For any open neighborhood `G` of a concrete determinant-sector,
nonzero-pivot `Case2PassiveTheta` point `z0`, there is a smaller open
neighborhood `V subset G` on which:

```text
1. the endpoint-sector topology-tuple image is measurable,
2. the endpoint topology tuple lies in the determinant chart pointwise,
3. the raw-order p.13 chart agrees pointwise with the direct endpoint source
   chart,
4. the direct source-chart pushforward agrees with both the one-stage
   raw-order-composite pushforward and the two-stage raw-order pushforward
   for every source measure restricted to V.
```

## Lean

```text
DLNFibre.DLN.Aoyagi.exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

## Existing Inputs

The slice uses:

```text
exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
continuous_case2PassiveThetaEndpointTopologyTuple
continuous_topologyTupleEdgeRawOrder_detChart_subtype
continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
continuous_ofTopologyTuple
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
AEMeasurable.map_map_of_aemeasurable
Measure.map_congr
```

## Proved

The theorem proves a relative local shrink.  The same open set `V` carries the
endpoint-sector measurability statement, pointwise determinant-chart
membership, all pointwise raw-order/source-chart readback identities, and the
one-stage/two-stage pushforward equalities for every
`sourceMeasure.restrict V`.

## Assumed

The theorem assumes the determinant-sector condition and selected pivot
nonvanishing at the base point, the standard topological and measurable
instances needed for the concrete theta and raw tuple spaces, and the open
neighborhood `G` of the base point.  The source measure is not used to choose
`V`; it is quantified afterward in the final pushforward clause.

## Cited

None.  This is an internal local chart and measure-functoriality statement.

## Deferred

No determinant-chart Haar transport, raw-order Haar transport, original DLN
source-prior identification, exact passive-sector pushforward,
source-image equality, source-rank coverage, normal-crossing construction,
pole-order theorem, or RLCT extraction is proved here.

## Route

First normalize the existing passive-theta pointwise raw-order bridge into an
explicit concrete existential, then destructure it.  Intersect its open set
with the caller's open neighborhood and run the relative endpoint-sector
measurability theorem inside that intersection.  The restricted open set
inherits the pointwise bridge, and the pushforward identities follow from
continuity-on-subtypes, a.e. support in the raw-order chart domain, map-map
associativity, and map congruence.

## Verification

Passed during construction:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
./scripts/sorries
git diff --check
```

`./scripts/sorries` reported a clean placeholder/debug-marker inventory.
