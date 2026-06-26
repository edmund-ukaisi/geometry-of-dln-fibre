# A2 retained-passive selected-entry source-readback residual-factor handoff

## Boundary

This slice is a selected-entry consumer of the retained-passive
source-readback residual readout.  It does not construct the retained-passive
source chart, prove source/image equality, prove a weighted pushforward or
Jacobian formula, compare the original DLN loss, prove normal crossings,
compute pole order, or extract an RLCT.

## Pen-and-paper reproduction

The retained-passive selected-entry local-measure theorem previously assumed
the raw square-sum residual readout

```text
sum_c residualCoord(sourceChart(y))_c^2 = residual_selected(pivot,y).
```

The preceding retained-passive readout theorem gives, for

```text
E_y = fixedBaseEdgeMatrix(Cedge(sourceChart(y))),
```

the identity

```text
residualCoord(sourceChart(y))
  = entries(residualFactorProduct((sourceReadback E_y).C, last, 0)).
```

Therefore it is enough to supply the entrywise selected-entry matrix identity

```text
residualFactorProduct((sourceReadback E_y).C, last, 0)
  = matrix(c |-> CenterCoord.chartMap(pivot,y,e(c))).
```

Here `e` is the finite equivalence from the endpoint residual coordinate index
to the selected center.  Taking scalar entries gives

```text
residualCoord(sourceChart(y))_c
  = CenterCoord.chartMap(pivot,y,e(c)).
```

The finite square-sum is invariant under the reindexing `e`, hence

```text
sum_c residualCoord(sourceChart(y))_c^2
  = sum_i CenterCoord.chartMap(pivot,y,i)^2
  = CenterCoord.residual(pivot,y).
```

The last equality is the already proved selected-entry identity
`CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`.

The new local-measure theorem calls the previous selected-entry retained-
passive handoff with this derived residual square-sum equality.

## Kill conditions

- If the supplied matrix identity compares the factor product with raw `y`
  rather than `CenterCoord.chartMap pivot y`, the square-sum target is wrong.
- If the residual-coordinate equivalence does not cover the whole endpoint
  residual coordinate index, the reindexing step cannot be used.
- This does not prove that the supplied factor identity follows from a
  particular Aoyagi Case 2 source construction; that remains a separate
  source-specific readout theorem.
