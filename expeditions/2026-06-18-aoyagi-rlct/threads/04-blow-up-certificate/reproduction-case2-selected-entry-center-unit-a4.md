# Reproduction - A4 Case 2 selected-entry center unit factor

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

## Source Anchor

Aoyagi PDF p. 5 defines the ideal convention using the sum of squares of
analytic generators.  In Case 2 on PDF pp. 19-21, the displayed
selected-entry chart sends the top-left residual-block entry to
`u_{S,J+1}` and every other residual-block entry to `u_{S,J+1}` times a
new residual coordinate.

The previous slice proved the finite algebraic identity

```text
sum x_i^2 = u^2 * (1 + sum y_i^2)
```

for this selected-entry chart.  This slice checks the next elementary fact:
over an ordered field, the normalized factor

```text
1 + sum y_i^2
```

is nonzero, hence a unit in the field.

## Pen-and-Paper Calculation

Let `E` be a finite set of non-pivot residual coordinates and let
`y_i` be their values.  In any ordered commutative semiring with the usual
ordered-ring-style square-nonnegativity facts,

```text
y_i^2 >= 0
```

for every `i`.  Therefore the finite sum is nonnegative:

```text
sum_{i in E} y_i^2 >= 0.
```

Since `1 > 0`, we get

```text
1 + sum_{i in E} y_i^2 > 0.
```

Thus this factor is nonzero.  If the coefficient ring is an ordered field,
every nonzero element is a unit, so

```text
IsUnit (1 + sum_{i in E} y_i^2).
```

For Aoyagi's displayed Case 2 chart, take

```text
E = case2ResidualBlockPivotEntries n S J \ {(J+1,J+1)}.
```

Under the displayed-pivot hypotheses, this is exactly the normalized factor in
the selected-entry center square identity.  The proof of nonvanishing itself
does not use the shape of the finite set; it only uses that it is finite and
that the coefficient field is ordered.

## Boundary

This proves only the nonvanishing/unit property of the selected-entry
center-square factor.  It does not prove:

- an analytic chart neighbourhood;
- chart coverage or transition regularity;
- a differentiable Jacobian or volume-form theorem;
- unit control for Aoyagi's later `P` and `Q` regular changes;
- a full `AoyagiNormalCrossingChartCertificate`;
- pole order or RLCT extraction.

The result supplies one local unit factor needed by a later A0 chart
certificate, not the chart certificate itself.

## Lean Names

```text
selectedEntryCenterSq_nonneg
selectedEntryCenterSqUnitFactor
selectedEntryCenterSqUnitFactor_pos
selectedEntryCenterSqUnitFactor_ne_zero
selectedEntryCenterSqUnitFactor_isUnit
case2DisplayedSourceChartMap_centerSqUnitFactor_pos
case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero
case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit
```

## Kill Conditions

- Do not use this as a proof of analytic chart coverage.
- Do not use this as a proof of the total loss unit in an A0 chart unless all
  other local factors, including regular `P` and `Q` changes, have also been
  supplied.
- Do not use this over unordered coefficient rings or over arbitrary fields
  such as complex fields, where `1 + sum y_i^2` can vanish.
