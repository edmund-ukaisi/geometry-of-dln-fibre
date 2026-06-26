# A2 retained-passive Case 2 pivot-nonzero source readout

## Boundary

This slice is finite selected-entry inverse algebra.  It replaces the previous
entrywise successor-source readout hypothesis by a single fixed-pivot
nonzero hypothesis for the displayed post-pivot Case 2 product.

It does not prove that the fixed pivot is nonzero.  It does not construct the
retained-passive source chart, identify a longer retained-passive suffix with
the two-edge Case 2 chain, prove source image coverage, prove measure
pushforward or Jacobian transport, compare the original loss, prove normal
crossings, compute pole order, or extract an RLCT.

## Pen-and-paper reproduction

Let `center` be the finite successor residual center

```text
case2ResidualBlockPivotEntries n S (J+1).
```

Its displayed pivot is

```text
pivotNext = (J+2,J+2).
```

The center-coordinate selected-entry chart with this pivot is

```text
chartMap(pivotNext,y)(pivotNext) = y(pivotNext),
chartMap(pivotNext,y)(c) = y(pivotNext) * y(c)  for c != pivotNext.
```

For any target value `v : center -> R` with `v(pivotNext) != 0`, define

```text
y(pivotNext) = v(pivotNext),
y(c) = v(c) / v(pivotNext)  for c != pivotNext.
```

Then the chart map recovers `v`:

```text
chartMap(pivotNext,y)(pivotNext) = v(pivotNext),
chartMap(pivotNext,y)(c)
  = v(pivotNext) * (v(c) / v(pivotNext))
  = v(c).
```

In the Case 2 post-pivot setting, an endpoint equivalence

```text
eNext : tau ~= Case2ResidualColIndex n S (J+1)
```

turns the product matrix

```text
P = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
```

into a center-indexed value by

```text
v(c) = P ((coordEquiv.symm c).row) ((coordEquiv.symm c).col),
```

where

```text
coordEquiv =
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J+1) (Equiv.refl _) eNext.
```

If this value is nonzero at `pivotNext`, the previous inverse produces
`yNext : center -> R` such that for every row `i` and free endpoint `t`,

```text
P i t =
  chartMap(pivotNext,yNext)(coordEquiv(i,t)).
```

The existing definitional bridge between `case2DisplayedSourceChartMap` and
`SelectedEntrySignedBox.CenterCoord.chartMap` rewrites this as exactly the
successor-source entrywise readout used by the retained-passive Case 2 bridge.

Finally, the already-proved synthetic retained-passive datum theorem consumes
that entrywise readout and returns the residual-factor product matrix identity
for `case2PostPivotRetainedPassiveData`.

## Checks

- In the nonzero-pivot branch, the fixed-pivot nonzero hypothesis replaces
  the supplied entrywise source-chart readout, but it is still an explicit
  hypothesis.
- The theorem fixes the successor pivot `(J+2,J+2)`, matching the successor
  center `(S,J+1)`.
- The endpoint equivalence `tau ~= Case2ResidualColIndex n S (J+1)` remains
  explicit.
- The result is finite algebra over the selected-entry chart map, not source
  production or analytic chart coverage.
