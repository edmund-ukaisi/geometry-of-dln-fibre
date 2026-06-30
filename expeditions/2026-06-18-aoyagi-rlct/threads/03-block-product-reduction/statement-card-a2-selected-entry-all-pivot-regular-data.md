# Statement card - A2 selected-entry all-pivot regular data

Date: 2026-06-29.

## Statement

For a nonempty finite selected-entry center and a supplied enumeration of all
center entries, the all-pivot selected-entry chart-family certificate supplies
chart regularity and unit regularity over the same shared universal-domain
context used by the all-pivot source-coverage theorem.

Lean names:

```text
selectedEntryAllPivotAnalyticChartRegularData
selectedEntryAllPivotAnalyticUnitRegularData
selectedEntryAllPivotAnalyticChartRegular
selectedEntryAllPivotAnalyticUnitRegular
```

## Source reference

Aoyagi PDF pp. 15-22 uses the selected-entry blow-up chart

```text
x_p = u,
x_i = u r_i      for i != p.
```

The regularity calculation is elementary chart-by-chart continuity for this
formula and for the unit factors `1 + sum r_i^2` and `1`.  The all-pivot
family is expedition-built finite data obtained by varying the displayed
selected-entry formula over possible pivots.

## Dependencies

- `selectedEntryAllPivotAnalyticAtlasContext`
- `continuous_formalChartMap`
- `continuous_chartPointCoord`
- `continuous_chartPointLossUnit`
- `continuous_chartPointJacobianPriorUnit`
- the certificate fields `lossUnit_isUnit` and `jacobianPriorUnit_isUnit`

## Nonclaims

This does not prove transition regularity, Jacobian/volume compatibility,
source production, branch termination, normal-crossing extraction, pole order,
or RLCT.  It also does not identify an external/original source prior or
construct the full `SelectedEntrySuppliedAnalyticAtlasProducer`.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-regular-data.md
```

Review:
`threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-regular-data.md`;
PASS by xhigh source/scope reviewer `Maxwell the 4th` and xhigh Lean/API
reviewer `Sartre the 4th`.
