# Pen-and-paper reproduction - A4 continuing certificate without chart family

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-continuing-certificate-without-chart-family-a4.md`.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The continuing branch uses the displayed
top-left chart, the row/column operations `P`, `Q`, the transported following
factor `C' = Q^-1 C`, and then reads the pivot-first product as the next
same-stage `(S,J+1)` source product.

This note records only the local finite certificate packaging for that
continuing branch.  It does not prove chart coverage or source production of
the successor chart object.

## Dependency Audit

The structure

```text
Case2DisplayedContinuingReindexedSourceChartCertificate
```

contains the following fields:

- displayed pivot membership and chart-map values;
- finite selected-entry principalization of the current residual-block center;
- the concrete `case2Succ` post-weight update;
- nonemptiness of the next residual-block center under `J+2 <= M(S+1)`;
- the reindexed next-source-product identity;
- corrected exponent, level, least-value-gap, and recurrence-gap post-data;
- the new-numerator equality with the current center cardinality.

None of these fields mention chart regularity or transition regularity.

Before this slice, the constructor

```text
sourceChartMap_continuingReindexedSourceChartCertificate
```

asked for a `Case2ResidualBlockChartFamilyBoundary` only because it called the
older reindexed-product theorem

```text
sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData.
```

After the direct theorem

```text
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData
```

the certificate constructor can use the same finite inputs without a chart
family boundary.

## Field Reproduction

Let

```text
upivot = case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1).
```

The displayed pivot membership and chart-map value fields come from the
source-coordinate selected-entry chart calculation:

```text
case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
case2DisplayedSourceChartMap_pivot
case2DisplayedSourceChartMap_of_ne
```

The selected-entry principalization fields are finite algebra:

```text
case2DisplayedSourceChartMap_value_mem
case2DisplayedSourceChartMap_center_dvd
case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton
```

The post-weight field follows from the concrete `case2Succ` recurrence
post-data and the actual-width label for `(S,J+1)`:

```text
pre.case2Succ_case2SuppliedPostData upivot
actualWidthLabel_case2_new
Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge
```

The next-center nonemptiness is the finite continuation guard:

```text
case2DisplayedPostPivotResidualBlock_nonempty_of_next
```

The product and post-data fields are now supplied directly by:

```text
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData.
```

The new numerator/center-cardinality equality is:

```text
correctedCase2NewLabelNumerator_eq_card_of_cont.
```

Thus the constructor does not need a chart-family boundary.

## Ordered-Field Refinements

The unit and center-square/formal-Jacobian constructors also do not need chart
regularity once the base continuing certificate is direct.  Their extra fields
are:

```text
case2DisplayedSourceChartMap_centerSqUnitFactor_pos
case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero
case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit
case2DisplayedSourceChartMap_centerSq
case2DisplayedSourceChartMap_pivotFirstJacobian_det
case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one
Finset.card_erase_add_one
```

All are finite selected-entry algebra, not chart regularity.

## Lean Target

```text
sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily
sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily
sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily
```

The existing chart-family-bearing constructors should remain as compatibility
wrappers delegating to the direct versions.

## Boundary Checks

- This removes only a vacuous current chart-family dependency from local
  finite certificate constructors.
- It does not source-produce `Csucc`, successor chart families, suffixes, or
  terminal branch data.
- It does not prove chart coverage, transition regularity, analytic
  Jacobian/volume-form data, normal crossings, pole order, or RLCT.
- It does not repair the printed Case 2 vector mismatch; it continues to use
  the corrected prefix-minimum post-data isolated earlier.

## Kill Conditions

- Kill the slice if any new direct constructor still has `ChartRegular`,
  `TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary` arguments.
- Kill the slice if the proof calls
  `Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
  or relies on a trivial chart-family witness.
- Do not rename the result as source production or an A0 normal-crossing
  certificate.
