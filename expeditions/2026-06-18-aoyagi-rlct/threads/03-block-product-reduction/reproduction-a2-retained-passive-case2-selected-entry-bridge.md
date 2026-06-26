# A2 retained-passive Case 2 selected-entry bridge

## Boundary

This slice is finite Case 2 residual-factor algebra.  It does not construct
retained-passive source data, prove source image equality, prove a weighted
pushforward or Jacobian formula, compare the original DLN loss, prove normal
crossings, compute pole order, or extract an RLCT.

It is explicitly a two-edge statement.  The retained-passive endpoint family is
`Fin 3`; this is the post-pivot Case 2 chain

```text
free endpoint -> residual columns -> residual rows.
```

No theorem in this slice transports a longer retained-passive suffix to that
two-edge chain.

## Pen-and-paper reproduction

In the post-pivot Case 2 step, Aoyagi's continuing residual block is not the
old `(S,J)` residual block.  It is the shifted block on the `(S,J+1)` domains.
The two endpoint types are:

```text
Case2ResidualColIndex n S (J+1)
Case2ResidualRowIndex n S (J+1).
```

The two-edge factor family is ordered from right to left in the residual-factor
product.  For a retained-passive coordinate datum `data` with `C`-factors
indexed by `Fin 2`, the product from endpoint `0` to endpoint `2` unfolds as

```text
residualFactorProduct(data.C, 2, 0) = data.C 1 * data.C 0.
```

The Case 2 identifications are therefore:

```text
data.C 1  =  displayed post-pivot residual block D_(J+1),
data.C 0  =  displayed free following factor C'_+.
```

The order is load-bearing.  Swapping these factors would give
`C'_+ * D_(J+1)`, which is not type-correct under the displayed endpoint
orientation and is not Aoyagi's post-pivot lower product.

After reindexing endpoints by equivalences

```text
e2 : Case2ResidualRowIndex n S (J+1) ~= kappa_2,
e1 : Case2ResidualColIndex n S (J+1) ~= kappa_1,
e0 : tau ~= kappa_0,
```

the existing finite product bridge says that the residual-factor product is
the selected-center coordinate matrix whenever the displayed product entries
are the selected-center coordinates:

```text
D_(J+1) * C'_+  at (i,t)
  = CenterCoord.chartMap(pivot,y)(residualCoordEquiv(e2 i, e0 t)).
```

This gives the generic retained-passive data-level bridge:

```text
residualFactorProduct(data.C, 2, 0)
  = matrix(c |-> CenterCoord.chartMap(pivot,y,residualCoordEquiv(c))).
```

There is also a source-shaped successor-center version.  Here the center is

```text
case2ResidualBlockPivotEntries n S (J+1),
```

and the selected pivot is `(J+2,J+2)`.  The entrywise hypothesis is stated in
Aoyagi's displayed source-chart language:

```text
D_(J+1) * C'_+ at (i,t)
  = case2DisplayedSourceChartMap n hS hnext
      yNext_(J+2,J+2)
      (CenterCoord.sourceResidual yNext)
      (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J+1) refl eNext (i,t)).1.
```

The theorem concludes the corresponding successor selected-entry
`CenterCoord.chartMap` matrix, with endpoint equivalence

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J+1) e2.symm (e0.symm.trans eNext).
```

The old `(S,J)` center and pivot are not used in this conclusion.

## Kill conditions

- The retained-passive endpoint family must be a two-edge `Fin 3` family.
- `data.C 1` is the post-pivot residual block and `data.C 0` is the following
  factor; reversing them is wrong.
- The successor theorem targets `(S,J+1)` and pivot `(J+2,J+2)`, not the old
  `(S,J)` center.
- The entrywise selected-center readout is still a supplied mathematical
  hypothesis.  This slice only removes residual-factor-product boilerplate.
