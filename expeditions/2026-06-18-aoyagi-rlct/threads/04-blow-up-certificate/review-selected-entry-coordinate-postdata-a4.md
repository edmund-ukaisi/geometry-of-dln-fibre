# Review - Selected-entry coordinate postdata

Date: 2026-06-24.

Reviewer: xhigh independent checker `Herschel the 2nd`.

## Verdict

QUALIFIED PASS after source-wording correction.

The coordinate equalities are mathematically correct and match the Lean
definitions.  The generic selected-entry chart certificate stores the
exceptional coordinate as the unique chart coordinate; `sourceChartPoint`
stores first coordinate `u`; and `sourceChartTransitionPoint` stores first
coordinate `u * denom`.

## Required Corrections

The source anchor must distinguish what Aoyagi prints from what Lean
generalizes.  Aoyagi PDF pp. 19-22 support the displayed Case 2 top-left pivot
chart.  The arbitrary all-pivot target statement is the Lean selected-entry
finite generalization, not a claim that Aoyagi displays every target pivot.

The word `overlap` should be reserved for the case where the denominator is
nonzero.  The coordinate-value theorem itself does not need a nonzero
hypothesis because the transition-generated target point is a formal chart
point; chart-map equality, inverse laws, and analytic transition statements
need nonvanishing hypotheses.

The Lean statements should keep the coordinate index `(0 : Fin 1)` explicit.

## Lean Readiness

The checker confirmed that Lean can add the proposed four theorems:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq_sourceSelected
```

The generic statements are definitional.  The Case 2 wrappers should use the
generic theorems by `simpa` rather than raw `rfl` over the Case 2 abbreviation.

## Nonclaims

No analytic chart domains, chart coverage, transition regularity, source
production, analytic Jacobian theorem, normal crossings, pole order, or RLCT.

