# Reproduction - A4 Case 2 corrected weight scalar transport

Date: 2026-06-25.

Status: Lean target implemented as finite algebra.

## Source Anchor

Aoyagi PDF pp. 19-21, Case 2.  The displayed selected-entry chart writes the
old residual block as

```text
D_J = u_{S,J+1} N
```

where the normalized matrix `N` has top-left entry `1`.  The paper then sets,
on p. 20,

```text
b'_i = u_{S,J+1} b_i,  i = J+1,...,M(S).
```

It defines the column operation

```text
Q = [1  -y; 0  I],
```

so that `D''_J = N Q`, and transforms the following factor by

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

On p. 21 the row operation `P` clears the first column below the pivot and the
cleared block is

```text
D'''_J = [1 0; 0 D_{J+1}].
```

The printed p. 21 display carries an extra final `u_{S,J+1}`.  With the p. 20
definition `b'_i = u_{S,J+1} b_i`, the algebraically consistent identity has
that scalar already absorbed into the diagonal weights.  Counting it again
would square the selected variable.

## Pen-And-Paper Calculation

Write

```text
N = [1 y; x D],
Q = [1 -y; 0 I],
Q^-1 = [1 y; 0 I].
```

Then

```text
N Q = [1 0; x D - x y].
```

If `C = Q C'`, then the raw block and old weights satisfy

```text
diag(b) (u N) (Q C')
  = diag(u b) N Q C'.
```

Now suppose the lower transported weights are quotient multiples of the
pivot transported weight:

```text
u b_i = q_i (u b_0).
```

The row operation

```text
P = [1 0; -q_i x_i I]
```

then gives

```text
P diag(u b) (N Q)
  = diag(u b) [1 0; 0 D - x y].
```

Combining the two equalities gives the corrected source-side identity

```text
(P diag(b) (u N)) (Q C')
  = diag(u b) [1 0; 0 D - x y] C'.
```

There is no additional final factor of `u`.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:

```text
weightedPivotDiagonal_mul_smul
weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ
```

The first theorem proves

```text
weightedPivotDiagonal b0 b * (u • M)
  = weightedPivotDiagonal (u*b0) (fun i => u*b i) * M.
```

The second theorem combines that scalar transport with the existing normalized
`Q/P` identity:

```text
(P * weightedPivotDiagonal b0 b * (u • pivotPreQBlock x y D)) * (Q * C')
  =
(weightedPivotDiagonal (u*b0) (fun i => u*b i)
    * weightedPivotClearedBlock (D - x*y)) * C'.
```

The quotient hypothesis is exactly

```text
u * b i = q i * (u * b0).
```

## Nonclaims

- No chart coverage or analytic atlas construction.
- No source production of `C'`.
- No successor chart-family construction.
- No residual-index equivalence.
- No Jacobian/density theorem.
- No normal-crossing certificate, pole order, or RLCT extraction.
- No theorem reproducing the printed p. 21 extra-`u` display under the p. 20
  convention `b'_i = u b_i`.
