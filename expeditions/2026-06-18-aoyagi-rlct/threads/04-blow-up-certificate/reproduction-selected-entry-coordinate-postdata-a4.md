# Reproduction - Selected-entry coordinate postdata

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The finite selected-entry normal-crossing certificates already record chart
maps, loss monomial identities, formal Jacobian/prior monomial identities, and
local exponent data.  For later A0 chart-certificate consumers, we also need
the concrete value of the unique chart coordinate.

This slice records only coordinate postdata:

```text
coord = u
```

at a source selected-entry chart point, and

```text
coord = u * denom
```

at a transition-generated target chart point.

## Source Anchors

Aoyagi PDF pp. 19-22, Case 2 selected-entry blow-up calculation, support the
displayed top-left pivot chart.  In that selected pivot chart, the pivot entry
is written as the exceptional coordinate `u`, and the other selected center
entries are written as `u` times normalized coordinates.

The Lean all-pivot finite selected-entry family generalizes this finite chart
algebra to every pivot of a finite center.  This all-pivot version is a Lean
finite selected-entry generalization, not a claim that Aoyagi displays every
target pivot chart.  The Case 2 specialization rewrites the generic normalized
coordinate as

```text
case2SourceSelectedNormalizedMapOfMem sourcePivot residual targetPivot.
```

## Pen-and-paper Calculation

Let `I` be a finite selected-entry center and choose a pivot `p in I`.  The
selected-entry chart has coordinates

```text
x_p = u,
x_i = u y_i     for i != p.
```

The finite normal-crossing chart certificate stores a single coordinate, the
exceptional coordinate:

```text
coord(source chart point) = u.
```

Now compare a source pivot `p` and a target pivot `q` in the Lean all-pivot
finite chart family.  In the source chart, the normalized value of `q` is

```text
denom = normalized_p(q).
```

The formal transition-generated target chart point is defined by

```text
u_target = u * denom,
y_target(i) = normalized_p(i) / denom.
```

Therefore the same certificate coordinate in the target chart is

```text
coord(target transition point) = u_target = u * denom.
```

No nonvanishing hypothesis is needed for this coordinate-value statement,
because the target chart point is a defined formal point.  To treat it as an
actual overlap point or to prove chart-map equality/inverse transition laws,
one must assume `denom != 0`.

For the Case 2 residual-block all-pivot certificate, if

```text
sourcePivot =
  finsetSubtypeChartEquiv(case2ResidualBlockPivotEntries n S J) sourceChart
targetPivot =
  finsetSubtypeChartEquiv(case2ResidualBlockPivotEntries n S J) targetChart,
```

then

```text
denom =
  case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1.
```

The Case 2 coordinate postdata is exactly:

```text
Cnc.coord sourceChart (sourceChartPoint ... sourceChart u residual) 0 = u

Cnc.coord targetChart
  (sourceChartTransitionPoint ... sourceChart targetChart u residual) 0
= u * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1.
```

## Lean Shape

Add generic selected-entry chart-family theorems in
`SelectedEntryNormalCrossing.lean`:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq
```

Then add Case 2 source-selected versions:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq_sourceSelected
```

These should be definitional consequences of the certificate's `coord` field
and the existing `sourceChartPoint` / `sourceChartTransitionPoint` definitions.
The coordinate index should remain explicit as `(0 : Fin 1)` in the Lean
statements.

## Nonclaims

- No analytic chart domains.
- No chart coverage.
- No transition regularity.
- No source production of successor matrices or suffixes.
- No analytic Jacobian/volume-form theorem.
- No global normal-crossing certificate.
- No pole order or RLCT extraction.
