# Statement card - A2 Case 2 source chart-point coverage

Date: 2026-06-29.

## Statement

For the Case 2 residual-block all-pivot selected-entry certificate, every
finite residual-block center value is represented by some chart-indexed source
point `sourceChartPoint n hS hcont c u residual`.  The unique certificate
coordinate of that witness is `u`.

Lean names:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq_sourceSelected
```

## Source reference

Aoyagi PDF pp. 19-22 for the displayed Case 2 selected-entry substitution

```text
x_p = u,
x_i = u r_i     for i != p.
```

The all-pivot statement is expedition-built finite coordinate bookkeeping
obtained by varying this displayed formula over possible residual-block pivots.
It is not a claim that Aoyagi prints an all-pivot analytic atlas.

## Dependencies

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`
- `case2ResidualBlockPivotEntries_nonempty_of_cont`
- `finsetSubtypeChartEquiv`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected`

## Nonclaims

This is finite residual-block chart-point coverage only.  It does not prove
analytic atlas coverage, transition regularity, source production of successor
matrices or suffixes, source-prior transport, normal crossings, pole order, or
RLCT.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-case2-source-chart-point-coverage.md
```

Review:

```text
threads/03-block-product-reduction/review-a2-case2-source-chart-point-coverage.md
```

Verdict: PASS after one nonblocking docstring wording repair.
