# A2 retained-passive raw-order two-stage pushforward

## Scope

This note hardens the raw-order map factorization by proving the same
restricted source pushforward through the intermediate raw-order tuple measure.
It is not a new Aoyagi source calculation.  The Aoyagi-dependent formulas are
the already reproduced retained-passive p.13 source/readback coordinates
(PDF pp. 10-13) and the Case 2 selected-entry punctured sector
(PDF pp. 19-22).  The new content is the local measurability needed to reassociate
two `Measure.map` operations.

## Objects

Use the same with-passive Case 2 coordinate domain as the previous checkpoint:

```text
X = eta x (center -> R),
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center.
```

For `z : X`, define:

```text
retainedData z =
  (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    n hS hcont hnext
    (A1passive z.1) (F2 z.1) (A3passive z.1)
    (Ctop z.1) (F3 z.1) z.2 eNext).endpointTransport e,

sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z),

tupleMap z =
  topologyTuple (retainedData z),

rawMap z =
  topologyTupleEdgeRawOrder (tupleMap z),

rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W2 B2 U0 hU0.
```

The topology-tuple punctured-sector theorem supplies an open set `V` containing
the base point such that, for every `z in V`,

```text
tupleMap z in topologyTupleDetChartSet,
rawMap z in topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart (rawMap z) = sourceChart z,
sourceChart z in retained-passive p.13 localSource,
sourceReadback(edgeMatrix(sourceChart z)) = retainedData z,
inverseReadout (sourceChart z) = z.2.
```

## Pen-and-paper measure calculation

Let

```text
nu = sourceMeasure.restrict V,
T = topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The first determinant-chart membership says that `tupleMap` lands in the
source domain of the raw-order partial chart on `V`.  Since `retainedData` is
continuous in the passive and residual coordinates, `tupleMap` is continuous.
Composing the restriction of `tupleMap` to `V` with the public continuous
raw-order map on the determinant-chart subtype gives

```text
rawMap is ContinuousOn V.
```

Because `V` is open, this gives

```text
rawMap is AEMeasurable with respect to nu.
```

The second membership gives `rawMap z in T` for all `z in V`, hence

```text
rawMap z in T for nu-a.e. z.
```

Pushing this almost-everywhere statement through the measurable map `rawMap`
gives

```text
y in T for (Measure.map rawMap nu)-a.e. y.
```

On `T`, the raw-order source chart is continuous.  Indeed, for `y in T`, first
apply `topologyTupleEdgeRawOrderInverse y`; the raw-order source-recursive
condition ensures that this inverse tuple lies in `topologyTupleDetChartSet`.
Then apply `ofTopologyTuple` and the direct retained-passive p.13 source chart.
All three maps are continuous on the relevant subtypes.  Therefore `rawChart`
is a.e. measurable with respect to `(Measure.map rawMap nu).restrict T`, and
the preceding support statement rewrites this restriction to
`Measure.map rawMap nu`.

Now the a.e. measurable map composition theorem applies:

```text
Measure.map rawChart (Measure.map rawMap nu)
  = Measure.map (fun z => rawChart (rawMap z)) nu.
```

The previous pointwise sector equality gives

```text
(fun z => rawChart (rawMap z)) = sourceChart
```

`nu`-almost everywhere, hence

```text
Measure.map (fun z => rawChart (rawMap z)) nu
  = Measure.map sourceChart nu.
```

Combining the two equalities proves the two-stage raw-order pushforward:

```text
Measure.map rawChart (Measure.map rawMap nu)
  = Measure.map sourceChart nu.
```

## Kill conditions

- Kill if this is described as a new Aoyagi source calculation.
- Kill if the equality is asserted without restricting to the punctured sector
  `V`.
- Kill if `Measure.map rawChart (Measure.map rawMap nu)` is formed without
  proving the separate a.e. measurability of `rawMap` and `rawChart`.
- Kill if raw-order support on `T` is silently treated as global continuity of
  `rawChart`; the proof must restrict to `T` and then remove the restriction by
  a.e. support.
- Kill if the theorem claims determinant-chart Haar transport, raw/source Haar
  transport, external/original source-prior comparison, a Jacobian density,
  source-image equality, source-rank coverage, normal crossings, pole order, or
  RLCT.

## Formalisation target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
```

Target name:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd
```

The statement returns the same open sector `V` and pointwise raw-order
membership/source-chart/readout fields as the one-stage theorem.  Under Borel
measurable structures on both the raw-order topology-tuple target and the
edge-family target, it proves:

```text
let nu := sourceMeasure.restrict V
let mu := Measure.map sourceChart nu
let muRawComp :=
  Measure.map (fun z : X => rawChart (rawMap z)) nu
let muRawTwoStage :=
  Measure.map rawChart (Measure.map rawMap nu)
muRawComp = mu and muRawTwoStage = mu.
```

It does not reprove the earlier local-source support or inverse-readout
pushforward fields for `mu`; those remain in the punctured-sector measure
readout theorem.
