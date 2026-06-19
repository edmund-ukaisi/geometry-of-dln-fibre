# A4 Case 2 Source-Substitution Weight Factoring

Status: checked finite algebra reproduction for the source-displayed Case 2
selected-entry chart.

## Scope

Aoyagi's displayed Case 2 pivot chart is on PDF pp. 19-21. The center is the
remaining residual block

```text
d_ij = 0,   J+1 <= i <= mu_S,   J+1 <= j <= n_(S+1),
```

and the displayed chart selects `d_(J+1,J+1)`.

This note proves only the elementary finite algebra that absorbs the selected
variable into row weights after the selected-entry substitution. It does not
construct the full source coordinate chart, top-row block identity, Jacobian,
arbitrary-pivot chart family, exponent update, or transition invariant.

## Reproduction

Let

```text
I = {i | J+1 <= i <= mu_S},
K = {j | J+1 <= j <= n_(S+1)}.
```

Fix the displayed pivot `(J+1,J+1)`. In the selected-entry chart, write the
selected variable as `u` and the normalised residual block as

```text
A : Matrix I K R,       A_(J+1,J+1) = 1.
```

The source-substituted residual block is

```text
D_src(i,j) = u * A(i,j).
```

This matches Aoyagi's `D_J = u_(S,J+1) D'_J` display, with `D'_J` normalised
at the selected pivot.

Let `w_i` be the old row weights on the residual rows. Then entrywise

```text
(diag(w) * D_src)_(i,j)
  = w_i * (u * A_(i,j))
  = (u * w_i) * A_(i,j).
```

Hence

```text
diag(w) * D_src = diag(i => u*w_i) * A.
```

After putting the displayed pivot first, this becomes

```text
(diag(w) * D_src).submatrix rowPivotFirst colPivotFirst
  =
weightedPivotDiagonal (u*w_pivot) (i => u*w_i)
  * pivotFirstMatrix A.
```

If `C0 : Matrix K T R` is the following factor before pivot-first reindexing,
then multiplication reindexing gives

```text
((diag(w) * D_src) * C0).submatrix rowPivotFirst id
  =
(weightedPivotDiagonal (u*w_pivot) (i => u*w_i)
  * pivotFirstMatrix A)
  * C0_pivot_first.
```

This is the source-variable bridge needed before the existing displayed Case 2
`Q/P` theorem. Under flat displayed residual-row weights, the previous theorem
then supplies the `P` witnesses and the `Q^{-1}` following-factor update.

## Normalisation Warning

Aoyagi prints both `b'_i = u b_i` on PDF p. 20 and a standalone factor `u`
before `diag(b')` in the p. 21 product display. This checkpoint uses the
consistent convention

```text
newWeight_i = u * oldWeight_i.
```

It does not encode an additional outside `u` multiplying `diag(newWeight)`.

## Lean Shape

Generic finite algebra:

```text
diagonal_mul_selectedEntrySubstitutionMatrix
pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix
```

Displayed Case 2 package:

```text
case2DisplayedSubstitutionMatrix
case2DisplayedSubstitutionMatrix_eq_mul_normalized
case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst
case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor
exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights
```

## Kill Conditions

- If the residual block has not already been identified with the source
  displayed Case 2 residual block, this theorem is only abstract finite matrix
  algebra.
- If the selected variable is counted both in `newWeight_i = u*oldWeight_i`
  and as a separate outside factor, this checkpoint is not the intended
  normalisation.
- If row weights are not flat in displayed residual-row coordinates, the final
  displayed `Q/P` wrapper does not apply.
- This theorem does not cover arbitrary selected residual-block pivots or the
  top `J` rows of the full source block identity.
