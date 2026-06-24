# Reproduction - A4 Case 2 chart-index source-selected boundary/QP bridge

Date: 2026-06-24.

Status: Lean formalised; focused/full build, sorry audit, and xhigh review
passed.

## Source Anchor

Aoyagi PDF pp. 19-21 uses the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and displays the selected-entry chart at the top-left residual pivot
`(J+1,J+1)`.  The Lean all-pivot finite selected-entry certificate indexes
the usual finite selected-entry charts over this printed center.  The
source-selected supplied-boundary package is still conditional: chart
regularity, transition regularity, recurrence post-data, and exponent
post-data remain supplied or concretely selected by its constructor.

## Reproduction

Let

```text
E = case2ResidualBlockPivotEntries n S J.
```

The all-pivot finite certificate enumerates its charts by the canonical
finite equivalence

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E.
```

Given a chart index

```text
c : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont).numCharts,
```

write

```text
p_c = finsetSubtypeChartEquiv E c : E.
```

Then

```text
p_c.2 : p_c.1 in case2ResidualBlockPivotEntries n S J
```

is exactly the pivot-membership input required by the source-selected Case 2
supplied-boundary constructor

```text
Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected.
```

Applying that constructor with `p = p_c.1` gives the supplied boundary whose
post recurrence state is `pre.case2Succ u` and whose exponent updates are the
corrected selected-label updates:

```text
t'          = updateSelectedLabelVector S (J+1) (correctedCase2PivotVector n S J) t,
numerator' = updateSelectedLabelScalar S (J+1)
                ((prefixMinNat n S - J) * (n(S+1)-J)) numerator,
leastValue'= updateSelectedLabelScalar S (J+1) J leastValue.
```

No new finite arithmetic is involved: the chart index only supplies the pivot
membership already chosen by the all-pivot certificate.

Projecting the existing source-selected theorem

```text
Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap
```

from this boundary gives the source-coordinate selected-pivot `Q/P` identity
in source-chart-map names for the chart-selected pivot.  The result is still
the existing finite source-selected matrix identity; the new bridge removes
only the manual resupply of the selected pivot membership.

## Lean Targets

Add the chart-index wrappers:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBoundary_of_chart_case2Succ_updateSelected
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected
```

## Boundary

- This is a chart-index-to-supplied-boundary adapter.
- Chart regularity and transition regularity remain supplied by
  `Case2ResidualBlockChartFamilyBoundary`.
- The recurrence and exponent post-data are the constructor's concrete
  `case2Succ` and corrected selected-label updates, not chart-produced data.
- This does not claim that Aoyagi displays non-top-left selected-entry pivot
  charts.
- This does not prove chart coverage, atlas construction, transition
  regularity, source production of successor matrices or suffixes, analytic
  Jacobian/volume control, global normal crossings, pole order, or RLCT.

## Kill Conditions

- Do not use this as a source-displayed arbitrary-pivot theorem.
- Do not use it to bypass the supplied `ChartRegular`/`TransitionRegular`
  predicates.
- Do not conflate finite selected-entry chart indexing with analytic atlas
  coverage or global normal-crossing extraction.
