# A2 full-to-adjacent-window outside-factor transport

## Boundary

This slice records the finite product bookkeeping needed before any longer
retained-passive suffix can use the adjacent Case 2 selected-entry readout.
It keeps the factors outside the adjacent two-edge window explicit.

It does not prove that those outside factors are identities, invertible,
absorbed by a chart, or irrelevant for the loss.  It also does not construct
endpoint equivalences, source charts, pivot nonzero hypotheses, analytic
transport, normal crossings, pole order, or RLCT extraction.

## Pen-and-paper reproduction

Let

```text
P(j,i) = residualFactorProduct(C,j,i)
```

be the decreasing residual-factor product.  Fix an adjacent window in a
longer chain:

```text
lo  = p
mid = p+1
hi  = p+2.
```

For any endpoints `i <= lo` and `hi <= j`, transitivity of the product gives
two splittings:

```text
P(j,i)  = P(j,hi) * P(hi,i),
P(hi,i) = P(hi,lo) * P(lo,i).
```

Substituting the second equality into the first gives the non-overclaiming
full-to-window decomposition

```text
P(j,i) = P(j,hi) * (P(hi,lo) * P(lo,i)).
```

The existing adjacent Case 2 theorem identifies only the middle factor
`P(hi,lo)` with the selected-entry center-coordinate matrix, after supplied
endpoint equivalences, supplied factor identities, and a supplied entrywise
readout.  Therefore the full-product consequence is exactly

```text
P(j,i) = P(j,hi) * (selected_center_matrix * P(lo,i)).
```

The outside products stay in the statement.

## Checks

- Factor order follows Aoyagi's decreasing suffix convention: the rightmost
  lower endpoint product is multiplied last.
- The selected-entry replacement is applied only to the adjacent two-edge
  product from `p+2` to `p`.
- No identity/absorption hypothesis for outside factors is introduced.
