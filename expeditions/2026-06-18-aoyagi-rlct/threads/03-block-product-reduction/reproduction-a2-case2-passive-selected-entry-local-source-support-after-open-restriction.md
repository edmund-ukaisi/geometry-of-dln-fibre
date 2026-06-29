# Reproduction - A2 Case 2 Passive Selected-Entry Local Source Support After Open Restriction

Date: 2026-06-29.

Status: controller reproduction before Lean formalisation.  This is measure
support after restricting the passive selected-entry coordinate domain to the
open determinant chart.  It is not source-prior transport or a Jacobian
calculation.

## Source Slice

Aoyagi pp. 10-13 motivate the retained-passive p.13 source variables and the
determinant-chart substitutions.  The preceding local source-readback theorem
has already extracted the elementary coordinate consequence needed here:
under continuity of the passive fields and determinant-unit hypotheses at one
base point, there is an open neighborhood on which the endpoint-transported
passive selected-entry source chart lies in the retained-passive local source.

This note only converts that pointwise local-source statement into support of
a pushed-forward measure after restricting the source-domain measure to the
same open set.

## Coordinate Domain

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
```

and define the passive selected-entry retained datum

```text
retainedData z =
  (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    ... (A1passive z.1) (F2 z.1) (A3passive z.1)
        (Ctop z.1) (F3 z.1) z.2 eNext).endpointTransport e.
```

The fixed-base source chart is

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z).
```

The previous theorem constructs

```text
U = (z |-> topologyTuple (retainedData z))^{-1}(topologyTupleDetChartSet)
```

with `IsOpen U`, `z0 in U`, and, for every `z in U`,

```text
sourceChart z in localSource
```

where

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource
    W2 B2 U0 hU0 (fun E => E).
```

It also proves the stronger pointwise readback identity on `U`, but the
measure-support handoff uses only the membership component.

## Measure Calculation

Let `sourceMeasure` be any measure on the passive selected-entry coordinate
domain.  We do not assume that the determinant-unit hypotheses hold away from
the base point.  Instead, restrict the domain measure to the open set `U`:

```text
restricted = sourceMeasure.restrict U.
```

Since `U` is open, it is measurable.  The standard restricted-measure fact
gives

```text
forall^ae z in sourceMeasure.restrict U, z in U.
```

Combining this with the pointwise source-membership theorem gives

```text
forall^ae z in sourceMeasure.restrict U,
  sourceChart z in localSource.
```

The source chart is a.e. measurable for the restricted measure.  This is not a
separate hypothesis: on `U`, the pointwise readback package gives
determinant-chart data; the determinant-chart subtype source-chart theorem
makes `sourceChart` continuous on `U`; and `ContinuousOn.aemeasurable₀`
applies to `sourceMeasure.restrict U`.

```text
AEMeasurable sourceChart (sourceMeasure.restrict U).
```

The generic retained-passive support helper then applies:

```text
(Measure.map sourceChart (sourceMeasure.restrict U)).restrict localSource
  =
Measure.map sourceChart (sourceMeasure.restrict U).
```

The helper uses measurability of `localSource`, which follows from continuity
of the identity edge-family realization `fun E => E`.

## Lean Target

The theorem should return the same open set and retain the pointwise
readback data:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
```

It should assume:

- continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`;
- determinant-unit hypotheses only at the base point `z0`;
- an arbitrary source-domain measure `sourceMeasure`;
- Borel/measurable-space structure on the source edge-family type, used to
  derive a.e. measurability from continuity on `U`.

It should prove:

- `IsOpen U`;
- `z0 in U`;
- pointwise local-source membership and readback equality for every `z in U`;
- support of `Measure.map sourceChart (sourceMeasure.restrict U)` on
  `localSource`.

## Nonclaims

This theorem does not prove global determinant-unit hypotheses, selected-entry
source-image equality, local coverage, source-rank coverage, determinant-chart
Haar pushforward, raw-Haar transport, source-prior transport, a Jacobian
change-of-variables formula, an exact localized residual marginal, normal
crossings, pole order, or RLCT extraction.
