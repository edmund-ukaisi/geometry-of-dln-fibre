# Reproduction - A2 Retained-Passive Fixed-Base Continuous Source Open Partial Homeomorph

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the ambient open-chart package
following the fixed-base continuous source homeomorphism.

## Question

The previous slice built a homeomorphism

```text
{data // data.detChart}  ~=  {E // E in SourceEdgeFamilySet}
```

where `SourceEdgeFamilySet` consists of continuous fixed-base reverse-edge
families whose extracted edge matrices satisfy the source-recursive
determinant-chart condition.

The ambient chart object should package the same maps as an
`OpenPartialHomeomorph` between:

```text
RetainedPassiveNonredundantCoordinateData
```

and continuous fixed-base reverse-edge families.

## Maps

The forward map is defined for every retained-passive coordinate datum, not
only for determinant-chart data:

```text
data |-> realise(data.edgeMatrix).
```

This is the prescribed fixed-base continuous reverse-edge family with matrix
family `data.edgeMatrix`.

The inverse map is defined for every continuous reverse-edge family:

```text
E |-> sourceReadback(edgeMatrix(E)).
```

No determinant-chart proof is needed to form this coordinate datum; the proof
is needed only to show that it lies in the open source domain.

## Source And Target

The source is exactly

```text
detChartSet.
```

The target is exactly

```text
SourceEdgeFamilySet =
  {E | edgeMatrix(E) in sourceRecursiveDetChartSet}.
```

The target is open because `sourceRecursiveDetChartSet` is open at the matrix
level and fixed-base edge-matrix extraction is continuous on continuous edge
families.

The parameterized local source already used by the measure handoff is the
preimage of this ambient target:

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge
  = Cedge^{-1}(SourceEdgeFamilySet).
```

This equality is definitional after unfolding the two sets.

## Inverse Identities

On the source, if `data.detChart`, then

```text
sourceReadback(edgeMatrix(realise(data.edgeMatrix))) = data.
```

This is the already-proved fixed-base retained-passive readback theorem.

On the target, if `edgeMatrix(E)` satisfies `sourceRecursiveDetChart`, then

```text
edgeMatrix(sourceReadback(edgeMatrix(E))) = edgeMatrix(E).
```

Realising both sides as continuous fixed-base edge families gives

```text
realise(edgeMatrix(sourceReadback(edgeMatrix(E)))) = realise(edgeMatrix(E)).
```

The left side is the forward map applied to the inverse datum, and the right
side is `E` by fixed-base realisation-after-extraction.

## Continuity

Forward continuity on the source follows by restricting to the determinant
chart:

```text
data |-> data.edgeMatrix
```

is continuous on `{data // data.detChart}`, and prescribed fixed-base
realisation is continuous in the matrix family.

Inverse continuity on the target follows by composing:

```text
E |-> edgeMatrix(E)
```

with the matrix-level source-recursive readback continuity.

## Boundary

This is an ambient open chart object for the explicit fixed-base
retained-passive source model.  It does not prove that arbitrary source-rank
points are in the target, does not give local source-rank coverage, does not
identify the target with the original DLN source image, does not assemble a
finite cover, and does not prove source-measure pushforward, density/Jacobian
transport, selected-entry residual-factor compatibility, normal crossings,
pole order, or RLCT extraction.
