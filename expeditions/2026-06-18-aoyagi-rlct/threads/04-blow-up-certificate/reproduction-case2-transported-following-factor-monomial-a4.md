# A4 Case 2 Transported Following Factor and Row-Index Monomial Weights

Status: checked finite algebra reproduction for the displayed Case 2 pivot.

## Scope

Aoyagi's displayed Case 2 calculation on PDF pp. 20-21 applies the column
operation `Q`, replaces the following factor by `Q^{-1} C`, and then applies
the lower row operation `P`. This note isolates the finite algebraic package:
name the transported following factor and supply quotient witnesses for `P`
from a monomial recurrence indexed by the residual source row.

This does not prove that Aoyagi's recursion has produced those row weights,
does not prove the Case 2 exponent update, and does not prove chart coverage,
regularity, termination, normal crossings, or RLCT extraction.

## Reproduction

Let the displayed normalised residual block be

```text
A : Matrix I K R,       A_(J+1,J+1) = 1,
```

where

```text
I = {i | J+1 <= i <= mu_S},
K = {j | J+1 <= j <= n_(S+1)}.
```

After pivot-first reindexing, write

```text
A = [ 1  y
      x  D ].
```

Aoyagi's column operation is

```text
Q    = [ 1  -y ],
       [ 0   I ],

Q^-1 = [ 1   y ],
       [ 0   I ].
```

The following factor supplied before pivot-first reindexing is first reindexed
to `C_pivot_first`. The displayed transported following factor is

```text
C_transported = Q^-1 * C_pivot_first.
```

This is the finite matrix object corresponding to the source line
`C'_J^(S+1) = Q^{-1} C_J^(S+1)`.

For the `P` row operation, suppose row weights have the form

```text
newWeight_i = u * b_i,
b_i = monomialRec step i,
```

where `i` is the residual source row label. The pivot row is `J+1`, and every
residual row satisfies

```text
J+1 <= i.
```

The monomial recurrence gives

```text
b_(J+1) divides b_i,
```

and multiplying both sides by the selected variable `u` gives

```text
u*b_(J+1) divides u*b_i.
```

Thus the quotient witnesses required by the normalised `P` identity exist.
Substituting these witnesses into the already-proved pivot-first `Q/P` product
identity gives

```text
(P * diag(u*b_(J+1), i => u*b_i) * A_pivot_first) * C_pivot_first
  =
(diag(u*b_(J+1), i => u*b_i) * cleared(A)) * C_transported.
```

Here `cleared(A)` is the block with lower-right part `D - x*y`. This is still
only local finite algebra in displayed Case 2 coordinates.

## Lean Shape

Lean records the row source label and its bound:

```text
case2ResidualRowLevel
case2ResidualRowLevel_ge
case2ResidualRowLevel_displayedPivotRow
```

It names the transported following factor:

```text
case2DisplayedTransportedFollowingFactor
```

and proves the row-index recurrence wrapper:

```text
exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec
```

The proof applies
`exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le` with
`level i = case2ResidualRowLevel ... i`.

## Kill Conditions

- If the row weights are not represented as `u * monomialRec step rowLevel`,
  this theorem does not apply.
- This theorem does not prove Aoyagi's source recurrence, the Case 2 gap
  `b_(J+1)=...=b_(mu_S)`, or equality of displayed row weights.
- This theorem does not include the top `J` rows of the full source blockdiag
  identity.
- This theorem does not prove arbitrary pivot charts, chart regularity,
  exponent updates, transition invariants, termination, normal crossings, or
  RLCT extraction.
