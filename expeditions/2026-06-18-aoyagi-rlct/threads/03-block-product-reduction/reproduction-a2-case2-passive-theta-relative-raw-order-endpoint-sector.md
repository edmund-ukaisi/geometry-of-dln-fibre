# Reproduction - A2 Case 2 passive theta relative raw-order endpoint sector

Date: 2026-06-30.

Status: pen-and-paper reproduction for a Lean slice in progress.

## Question

For the concrete `Case2PassiveTheta` endpoint chart, the current library has
two local facts:

```text
1. A pointwise raw-order/source-chart bridge on some open neighborhood Vraw.
2. Endpoint-sector image measurability after shrinking inside any prescribed
   open neighborhood G.
```

Can these be put on the same local open set, and can the one-stage and
two-stage raw-order pushforward identities be stated for every measure
restricted to that same set?

Answer: yes.  First obtain the raw-order bridge neighborhood `Vraw`.  Given
the caller's open neighborhood `G`, apply endpoint-sector measurability to

```text
Graw := G intersect Vraw.
```

The returned open set `V` satisfies `V subset Graw`, hence `V subset G` and
`V subset Vraw`.  The endpoint-sector image is measurable by construction,
and all pointwise raw-order/source-chart identities are inherited from
`Vraw`.

## Pointwise Data

On `Vraw`, the existing concrete passive-theta raw-order theorem gives, for
each `z`,

```text
endpointTopologyTuple z is in the determinant chart,
rawMap z is in the raw-order recursive determinant-chart set,
rawChart (rawMap z) = sourceChart z,
sourceChart z lies in the retained-passive p.13 local source,
sourceReadback (edgeMatrix (sourceChart z)) = retainedData z,
inverseReadout (sourceChart z) = z.yNext.
```

The relative theorem does not recompute these identities.  It records them on
the smaller `V` returned by the endpoint-sector measurability shrink.

## Measure Calculation

Let

```text
nu := sourceMeasure.restrict V,
mu := map sourceChart nu,
muRawComp := map (fun z => rawChart (rawMap z)) nu,
muRawTwoStage := map rawChart (map rawMap nu).
```

The pointwise identity on `V` implies

```text
(fun z => rawChart (rawMap z)) = sourceChart     nu-a.e.
```

because `nu` is the restriction to the open measurable set `V`.  Therefore

```text
muRawComp = mu
```

by measure map congruence.

For the two-stage identity, use local continuity:

```text
rawMap is continuous on V
```

because it is the continuous endpoint topology-tuple map followed by the
continuous raw-order map on the determinant-chart subtype, and the pointwise
determinant-chart membership holds on `V`.

Let

```text
T := topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The raw-order bridge gives `rawMap z in T` for every `z in V`, so

```text
map rawMap nu
```

is supported on `T`.  The raw chart is continuous on `T`: invert the raw-order
tuple inside the determinant-chart subtype, convert the topology tuple back to
retained-passive coordinate data, and apply continuity of the retained-passive
p.13 source chart.  Hence `rawChart` is a.e. measurable for `map rawMap nu`.
The standard map-map theorem gives

```text
map rawChart (map rawMap nu)
  = map (fun z => rawChart (rawMap z)) nu.
```

Combining this with `muRawComp = mu` yields

```text
muRawTwoStage = mu.
```

## Source Boundary

This is local chart-produced bookkeeping.  It combines an endpoint-sector
measurability shrink with raw-order source-chart identities on the same open
set.  It does not identify determinant-chart Haar measure, raw-order Haar
measure, an original DLN source prior, exact passive-sector pushforward,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.

## Lean Target

Add in `RetainedPassiveCase2PassiveThetaSourceMeasure.lean`:

```text
exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

The proof should:

```text
1. Type-normalize the existing pointwise raw-order bridge to the concrete
   passive-theta statement before destructuring it.
2. Apply the relative endpoint-sector measurability theorem to G intersect Vraw.
3. Use local continuity and a.e. map-map functoriality to prove both
   pushforward equalities.
```

## Kill Conditions

- Do not state source-prior transport.
- Do not state determinant-chart or raw-order Haar transport.
- Do not state exact passive-sector pushforward.
- Do not state source-image equality or source-rank coverage.
- Keep normal-crossing and RLCT extraction outside this slice.
