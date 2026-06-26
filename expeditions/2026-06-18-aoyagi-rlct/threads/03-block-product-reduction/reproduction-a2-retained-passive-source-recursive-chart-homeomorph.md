# Reproduction - A2 Retained-Passive Source-Recursive Chart Homeomorphism

Date: 2026-06-26.

Status: reproduced and formalised the topological packaging of the finite
two-sided source readback on the explicit recursive determinant chart.

## Question

The previous rung proved the finite right inverse

```text
(sourceReadback E).edgeMatrix = E
```

for every edge family `E` satisfying `sourceRecursiveDetChart`.  The earlier
left-inverse rung proved

```text
sourceReadback (data.edgeMatrix) = data
```

for every retained-passive coordinate point satisfying `data.detChart`.

The next question is whether these two finite inverse statements package as a
topological coordinate equivalence between the two explicit chart domains.

## Domains

The coordinate-side domain is the nonredundant retained-passive determinant
chart:

```text
{data // data.detChart}.
```

Here `data.detChart` means:

```text
IsUnit data.Ctop.det
and every passive A1 block has unit determinant.
```

The source-side domain is the source-recursive determinant chart:

```text
{E // sourceRecursiveDetChart E}.
```

This predicate says that every transformed edge visited by the deterministic
suffix-state readback recursion has an invertible selected top-left corner.

## Coordinate Source Lands In The Source Chart

Let `E = data.edgeMatrix`, with `data.detChart`.  The existing retained-passive
readback theorem for `data.toCoordinateData` says that for every edge `p`,
the transformed edge

```text
T_p = transformedEdge E p (suffixState E last p.succ)
```

has

```text
topLeftCorner T_p = data.toCoordinateData.solvedA1 p.
```

Thus it remains only to know that every solved full `A1` block has unit
determinant.  This is algebraic:

- passive solved `A1` blocks are the stored passive seeds;
- the active first block is `tail^-1 * Ctop`;
- the passive tail has unit determinant because it is a product of passive
  determinant-unit blocks;
- `Ctop` is a determinant unit by `data.detChart`.

Lean records this determinant-unit fact as

```text
solvedA1_det_isUnit_of_detChart.
```

It then proves

```text
sourceRecursiveDetChart_edgeMatrix_of_detChart.
```

This is the missing domain-membership direction for the coordinate source map.

## Continuous Maps Between Subtypes

The coordinate source map was already proved continuous on `{data //
data.detChart}` as a map into the ambient edge-family space.  The new
domain-membership theorem allows the codomain to be restricted:

```text
continuous_edgeMatrix_sourceRecursiveDetChart_subtype.
```

The source readback map was already proved continuous on the source-recursive
subtype as a map into the ambient coordinate space.  The previous determinant
propagation theorem says that `sourceReadback E` lies in `detChart`, so the
codomain can also be restricted:

```text
continuous_sourceReadback_detChart_subtype.
```

Both proofs are just subtype wrappers around the previously banked continuity
theorems.

## Homeomorphism

The two restricted maps are inverse by the already banked finite inverse
theorems:

```text
sourceReadback (data.edgeMatrix) = data
(sourceReadback E).edgeMatrix = E.
```

Therefore Lean defines the homeomorphism

```text
detChart_sourceRecursiveDetChart_homeomorph :
  {data // data.detChart} equiv_homeomorph {E // sourceRecursiveDetChart E}.
```

This is the first full topological packaging of the retained-passive
source-readback construction.

## Nonclaims

This homeomorphism is only between the named coordinate determinant chart and
the named source-recursive determinant edge chart.  It does not prove that
`sourceRecursiveDetChart` is open in the ambient edge-family space, that this
chart equals the whole source image, source-rank coverage, a global
source/image theorem, measure pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction.

