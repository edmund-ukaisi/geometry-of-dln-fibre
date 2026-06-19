# A4 Case 1(2) Displayed Row-Strip Weighted Source

Status: reproduced the elementary weighted source block for Aoyagi's
displayed Case 1(2) top-left pivot chart.

## Source Facts

Aoyagi's Case 1 uses the prefix-minimum residual row bound

```text
mu_S = M(S) = min { M^(q) | q <= S }
```

and actual source width in the next layer.  The residual block has rows
`J+1 <= i <= mu_S` and columns `J+1 <= j <= M^(S+1)`.

In Case 1, after choosing an old exceptional variable `u_(s,k)` with
`tilde_t_(s,k)=J+J1`, the blow-up center is

```text
d_ij = 0,    J+1 <= i <= J+J1,  J+1 <= j <= M^(S+1),
u_(s,k) = 0.
```

In Case 1(2), Aoyagi displays the top-left strip chart

```text
d_ij = u_(S,J+1) d'_ij
```

only for strip rows `J+1 <= i <= J+J1`, with the pivot normalised as
`d'_(J+1,J+1)=1`.  It also factors the hidden old variable as

```text
u_(s,k) = u_(S,J+1) u'_(s,k).
```

The matrix to which Aoyagi applies `Q` and `P` contains divided `d'` entries
only on the row strip.  Rows below the strip, `J+J1 < i <= mu_S`, remain
unprimed old `d` entries before the column operation.

## Pen-And-Paper Calculation

Let `u = u_(S,J+1)`.  Let `A` be the normalised matrix used before the
`Q` operation:

```text
A_(J+1,J+1) = 1,
d_ij = u A_ij        for J+1 <= i <= J+J1,
d_ij = A_ij          for J+J1 < i <= mu_S.
```

Let `c_i` be the row monomial after removing the single selected factor that
will be counted in the post row weights.  The old-variable factorisation gives

```text
oldWeight_i = c_i        on the row strip,
oldWeight_i = u c_i      below the row strip.
```

Then every residual row has the same weighted source expression:

```text
oldWeight_i d_ij = (u c_i) A_ij.
```

For strip rows, the `u` comes from the divided matrix entry.  For lower rows,
the matrix entry is unchanged and the `u` comes from the old variable
factorisation.  Therefore

```text
diag(oldWeight) D_chart = diag(i |-> u c_i) A.
```

After pivot-first reindexing, this is exactly the source equality required by
the generic displayed top-left adapter:

```text
weightedSource
  = weightedPivotDiagonal (u c_pivot) (i |-> u c_i)
      * pivotFirstMatrix(A).
```

If the pivot entry of `A` is `1`, then `pivotFirstMatrix(A)` is
`pivotPreQBlock x y D`.  If quotient witnesses satisfy

```text
u c_i = q_i (u c_pivot)
```

for all non-pivot rows, the existing finite `Q/P` algebra gives the displayed
source-order identity.  The selected variable is counted once in the row
weights.

## Lean Boundary

Lean now proves the elementary row-strip weighting identity in generic finite
matrix form:

```text
case1RowStrip_diagonal_mul_sourceMatrix
case1RowStrip_diagonal_mul_sourceMatrix_pivotFirst
case1RowStrip_weightedPivotFirstSubstitutionData
case1RowStrip_sourceOrder_identity
```

It also adds a Case 1-specific supplied-data boundary:

```text
Case1DisplayedRowStripSuppliedWeightedSourceData
```

with projections for the displayed continuation bound, displayed pivot center
membership, displayed pivot residual-block membership, and the supplied
source-order identity.

## Caveats

- This is not a selected-entry chart construction.
- This is not a full residual-block substitution theorem; Case 1(2) divides
  only the row strip.
- The hidden old label remains external to the `Unit` branch of the finite
  Case 1 center.
- Quotient regularity is supplied by witnesses; it is not derived here from
  recurrence data.
- No chart coverage, transition regularity, Jacobian calculation,
  normal-crossing statement, RLCT extraction, exponent post-data, or full
  transition invariant is proved here.
