# A2 retained-passive raw-order map factorization

## Scope

This note reproduces a measure-functoriality consequence of the
topology-tuple punctured-sector transport theorem.  It is not a new Aoyagi
source calculation.  The source-backed formulas are the already reproduced
retained-passive p.13 coordinates and Case 2 selected-entry readout.  The
present step records that, after restricting to the same punctured sector, the
chart-produced source pushforward can be presented as the pushforward by the
raw-order source-chart composite.

## Objects

Use the with-passive Case 2 coordinate domain

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

rawMap z =
  topologyTupleEdgeRawOrder (topologyTuple (retainedData z)),

rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W2 B2 U0 hU0.
```

Let `sourceMeasure` be an arbitrary measure on `X`.  The sector theorem gives
an open set `V` containing the base point such that every `z in V` satisfies

```text
rawMap z in topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart (rawMap z) = sourceChart z,
sourceChart z in retained-passive p.13 localSource,
sourceReadback(edgeMatrix(sourceChart z)) = retainedData z,
inverseReadout (sourceChart z) = z.2.
```

## Measure calculation

Let

```text
nu = sourceMeasure.restrict V.
```

Because `nu` is supported on `V`, the pointwise sector equality gives

```text
(fun z => rawChart (rawMap z)) = sourceChart
```

`nu`-almost everywhere.  Therefore, by congruence of pushforward measures,

```text
Measure.map (fun z => rawChart (rawMap z)) nu
= Measure.map sourceChart nu.
```

This is the one-stage raw-order composite factorization.  A two-stage
factorization

```text
Measure.map rawChart (Measure.map rawMap nu)
```

requires separate a.e. measurability of `rawMap` and `rawChart` with respect
to the intermediate pushed measure.  That is a valid later strengthening, but
the one-stage statement is the exact measure-level consequence needed here
and avoids importing any Haar/Jacobian machinery.

A separate earlier measure-readout theorem proves local-source support and
inverse-readout pushforward conclusions for the chart-produced source measure:

```text
mu.restrict localSource = mu,
Measure.map inverseReadout mu = Measure.map Prod.snd nu,
where mu = Measure.map sourceChart nu.
```

Those pushforward conclusions are not part of the present raw-order composite
factorization theorem.  The present theorem retains only the pointwise
local-source membership, source-readback equality, and selected-entry
inverse-readout equality needed to identify the composite on the restricted
sector.

## Kill conditions

- Kill if this is described as a new Aoyagi source calculation.
- Kill if the measure equality is asserted without restricting to the
  punctured sector `V`.
- Kill if the inverse readout is claimed without the selected-pivot nonzero
  condition built into `V`.
- Kill if the one-stage composite equality is described as two-stage
  `Measure.map` functoriality through an intermediate raw-order measure.
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
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_comp_eq_sourceChart_inverseReadout_eq_snd
```

The statement returns the open sector `V`, the pointwise raw-order
membership/source-chart/readout fields, and the measure equality

```text
Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V)
= Measure.map sourceChart (sourceMeasure.restrict V).
```

It does not retain the already proved local-source support and inverse-readout
pushforward fields for `mu = Measure.map sourceChart (sourceMeasure.restrict V)`;
those remain available from the earlier punctured-sector measure-readout
theorem.
