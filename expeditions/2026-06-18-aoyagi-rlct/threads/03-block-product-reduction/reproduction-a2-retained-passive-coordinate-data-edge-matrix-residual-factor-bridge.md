# A2 retained-passive coordinate-data edge-matrix residual-factor bridge

## Boundary

This slice is a source-map inverse reduction for the retained-passive
selected-entry residual-factor handoff.  It does not construct the selected-
entry source chart, prove the Case 2 displayed product identity, prove a
weighted pushforward or Jacobian formula, compare the original DLN loss, prove
normal crossings, compute pole order, or extract an RLCT.

## Pen-and-paper reproduction

The previous handoff asks for the source-readback matrix identity

```text
residualFactorProduct((sourceReadback E_y).C, last, 0)
  = matrix(c |-> CenterCoord.chartMap(pivot,y,e(c))),
```

where

```text
E_y = fixedBaseEdgeMatrix(Cedge(sourceChart(y))).
```

Suppose instead that a retained-passive coordinate datum `data_y` is supplied
for each selected-entry parameter `y`, and that it lies in the retained-
passive determinant chart.  Suppose also that it realizes the fixed-base edge
family:

```text
E_y = edgeMatrix(data_y).
```

The retained-passive source-readback inverse theorem says

```text
sourceReadback(edgeMatrix(data_y)) = data_y
```

on the determinant chart.  Therefore the source-readback residual-factor
product becomes the coordinate-data residual-factor product:

```text
residualFactorProduct((sourceReadback E_y).C, last, 0)
  = residualFactorProduct(data_y.C, last, 0).
```

Thus the source-readback matrix identity is reduced to the data-level identity

```text
residualFactorProduct(data_y.C, last, 0)
  = matrix(c |-> CenterCoord.chartMap(pivot,y,e(c))).
```

Combining this data-level identity with the previous retained-passive
source-readback selected-entry handoff gives the selected-entry residual
square-sum:

```text
sum_c residualCoord(sourceChart(y))_c^2 = CenterCoord.residual(pivot,y).
```

This is useful because the next Aoyagi-specific calculation should construct
or identify the concrete retained-passive coordinate data and prove the
identity for `data_y.C`, instead of reasoning through the opaque
`sourceReadback E_y` expression.

## Kill conditions

- The determinant-chart hypothesis on `data_y` is essential; without it the
  theorem `sourceReadback(edgeMatrix(data_y)) = data_y` is not available.
- The edge realization must be the fixed-base edge-matrix family used by the
  p.13 residual coordinate map, not a different edge convention.
- The data-level residual-factor product still must target
  `CenterCoord.chartMap pivot y`, not raw `y`.
- This does not prove the Case 2 entrywise product identity or construct the
  source chart; those remain the next source-specific algebra frontier.
