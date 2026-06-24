# Review - A4 selected-entry source-point coverage with coordinate

Date: 2026-06-24.

Reviewer: xhigh independent checker `Kierkegaard the 2nd`.

## Verdict

PASS with naming and scope corrections.

The proposed generic theorem is mathematically correct.  It combines the
existing finite source-point value production theorem with the definitional
coordinate projection for `sourceChartPoint`.

## Required Corrections

The checker recommended the name

```text
exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq
```

instead of the shorter `...and_coord_eq`, because the theorem explicitly
mentions the unique coordinate index `(0 : Fin 1)`.

The checker also recommended not adding a Case 1 specialization in this slice.
Such a wrapper would be a thin `simpa` specialization of the generic theorem,
and should wait until a downstream Case 1 theorem needs to avoid unfolding
`case1CenterGenerators_nonempty` and `finsetSubtypeChartEquiv`.

## Source Boundary

Aoyagi PDF pp. 15-18 support the selected-entry affine chart pattern in the
displayed Case 1 charts.  The all-pivot theorem is Lean's finite
selected-entry generalization, not a claim that Aoyagi prints every pivot
chart or proves analytic atlas coverage.

## Nonclaims

No analytic atlas coverage, transition regularity, source production,
analytic Jacobian theorem, normal crossings, pole order, or RLCT extraction.
