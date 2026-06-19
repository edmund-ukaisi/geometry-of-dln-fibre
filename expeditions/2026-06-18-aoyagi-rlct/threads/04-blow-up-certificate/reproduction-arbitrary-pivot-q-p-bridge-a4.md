# A4 Generic Pivot-First `Q/P` Algebra Bridge

Status: checked generic algebra bridge; not a source reproduction of arbitrary
non-displayed pivot charts.

## Scope

This note isolates the elementary algebra needed to apply the already-proved
normalised `Q/P` pivot identities after putting a chosen matrix pivot first.
Aoyagi displays only the top-left pivot `d_(J+1,J+1)` in Case 1(2) and Case 2;
the non-displayed pivot family is an inferred formalisation scaffold. This is
not a source reproduction of arbitrary pivot charts, not a chart-cover theorem,
not an affine blow-up atlas, and not a Case 1 or Case 2 transition theorem.

The source text is Aoyagi's blow-up proof:

- Case 1 center and Case 1(1)/(2) branches: PDF pp. 16-19.
- Case 2 center and pivot branch: PDF pp. 19-21.

## Source Data

At a state `(S,J)`, Aoyagi writes the active residual block as

```text
D_J = (d_ij),       J+1 <= i <= M(S),       J+1 <= j <= M^(S+1).
```

The source simultaneously uses actual widths `M^(s)` and prefix minima `M(S)`.
In this expedition notation, rows in the corrected residual block are bounded
by the prefix minimum `mu_S = prefixMinNat n S`, while columns use the actual
active width `n_(S+1)`.

In Case 1, Aoyagi blows up the center

```text
d_ij = 0,     i = J+1,...,J+J1,     j = J+1,...,M^(S+1),
u_(s,k) = 0,
```

where the old exceptional variable is chosen with
`\tilde t_(s,k) = J+J1` and a comparability/minimality condition. The displayed
Case 1(2) pivot chart selects the top-left strip entry `d_(J+1,J+1)`.

In Case 2, Aoyagi blows up the residual-block center

```text
d_ij = 0,     i = J+1,...,M(S),     j = J+1,...,M^(S+1),
```

and the displayed chart again selects the top-left entry `d_(J+1,J+1)`.

The paper then displays the same normalised top-left matrix algebra in
Case 1(2) and Case 2. In Case 2 this is the residual-block chart. In Case 1(2)
the selected row strip is divided by the pivot variable, while lower residual
rows are carried into the subsequent `Q/P` block. Thus the displayed algebra
should be read here as the already-normalised pivot block, not as a global
factorisation of every residual-block entry in Case 1(2):

```text
D = u * [ 1  y
          x  D_lower ],
Q = [ 1  -y
      0   I ],
D'' = [ 1  y
       x  D_lower ] Q
    = [ 1      0
        x  D_lower - x*y ],
```

followed by a lower-unitriangular matrix `P` that uses the quotients
`b'_i / b'_(J+1)` to clear the first column below the pivot:

```text
P * diag(b'_(J+1),...,b'_M) * D''
  = diag(b'_(J+1),...,b'_M) * [ 1  0
                                0  D_next ].
```

The current Lean identities formalise exactly this normalised displayed block,
with abstract lower-row type `rho` and lower-column type `kappa`.

## Reindexing Reproduction

Let `R` be a commutative ring, let `I` and `K` be finite row and column index
types, and choose a pivot row `i0 : I` and pivot column `j0 : K`. Let
`A : Matrix I K R` be a matrix whose selected pivot has already been normalised:

```text
A i0 j0 = 1.
```

Define the lower row and column index types by deleting the pivot:

```text
I0 = {i : I // i != i0},
K0 = {j : K // j != j0}.
```

Reindex `A` by putting the pivot first:

```text
A^pivot : Matrix (Unit ⊕ I0) (Unit ⊕ K0) R
```

with entries

```text
A^pivot (inl *) (inl *) = A i0 j0,
A^pivot (inl *) (inr j) = A i0 j,
A^pivot (inr i) (inl *) = A i j0,
A^pivot (inr i) (inr j) = A i j.
```

Set

```text
x i       = A i j0,      i : I0,
y j       = A i0 j,      j : K0,
D_lower i j = A i j.
```

Then, using only `A i0 j0 = 1`, the reindexed matrix is

```text
A^pivot = [ 1  y
            x  D_lower ],
```

which is exactly the input shape of the existing Lean definition
`pivotPreQBlock x y D_lower`.

Applying the existing `Q` theorem gives

```text
A^pivot * pivotQ y
  = [ 1        0
      x  D_lower - x*y ].
```

If weights on the lower rows satisfy

```text
b i = q i * b0        for every i : I0,
```

then the existing `P` theorem gives

```text
weightedPivotBlockRowOp q x * weightedPivotDiagonal b0 b *
    (A^pivot * pivotQ y)
  = weightedPivotDiagonal b0 b *
      weightedPivotClearedBlock (D_lower - x*y).
```

Equivalently, with a following factor `C`,

```text
(weightedPivotBlockRowOp q x * weightedPivotDiagonal b0 b * A^pivot) * C
  =
(weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D_lower - x*y)) *
  (pivotQinv y * C).
```

This gives the finite algebraic analogue of the displayed calculation after a
pivot-first blockification. The following factor `C`, the diagonal weights, and
the quotient witnesses must already be expressed in the same pivot-first row
and column coordinates. This does not assert that every non-displayed Aoyagi
selected-entry chart has source-proved regular coordinates or that these
reindexed blocks glue to an atlas.

## Aoyagi-Specific Interpretation

For Case 2, a selected entry `(i0,j0)` in
`case2ResidualBlockPivotEntries n S J` supplies a row in
`J+1..mu_S` and a column in `J+1..n_(S+1)`. A finite residual block using those
row and column subtype indices can be blockified so `(i0,j0)` is first. The
generic algebraic theorem can be applied only after separate proofs supply the
selected-entry chart, pivot normalization to `1`, coordinate transport for the
following factor and weights, and quotient witnesses showing that the selected
pivot-row weight divides every lower-row weight in the pivot-first order.

For Case 1(2), a selected strip entry `(i0,j0)` in
`case1StripEntries n S J J1` supplies a row in `J+1..J+J1` and a column in
`J+1..n_(S+1)`. Under the already-isolated row bound
`J+J1 <= mu_S`, it also lies in the residual-block row range. The same
pivot-first blockification applies to the corresponding finite residual block,
again only after separate chart, normalization, coordinate-transport, and
quotient-witness obligations are proved. For a non-top-left pivot row, the
denominator is the selected pivot-row weight, not automatically the displayed
`b'_(J+1)`.

The old-variable Case 1(1) branch is different: the selected generator is the
external `Unit` old exceptional variable, not a pivot entry in the residual
matrix. The pivot-first matrix reindexing lemma does not formalise that branch.

## What This Would Prove in Lean

The safest formal checkpoint is generic and purely algebraic:

```text
pivotFirstMatrix_eq_pivotPreQBlock
```

For finite row/column types, a matrix normalised at an arbitrary pivot becomes
`pivotPreQBlock` after the pivot-first reindexing.

A second corollary may package the already-proved `Q/P` theorem:

```text
weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
```

This says the normalised `Q/P` identity applies to the pivot-first reindexed
matrix under the same weight-divisibility hypothesis `b i = q i * b0`.

## Kill Conditions

- If the selected pivot is not a matrix entry, as in Case 1(1), this bridge is
  the wrong target.
- If the selected pivot value is not normalised to `1` after factoring the
  selected variable, `pivotPreQBlock` is not the correct block shape.
- If the selected pivot-row weight does not divide every lower-row weight in
  the pivot-first order, equivalently if witnesses `b i = q i * b0` are not
  supplied, the `P` clearing theorem does not apply.
- If the chosen Case 1 strip row is not proved to lie in the residual-block
  row range, the Aoyagi-specific instantiation is not source-valid.
- This bridge does not prove polynomial regularity of non-displayed selected
  charts, invertibility/Jacobian facts, chart coverage, exponent updates,
  termination, normal-crossing certificates, or RLCT extraction.
