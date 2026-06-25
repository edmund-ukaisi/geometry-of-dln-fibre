# Statement Card - A4 Case 2 corrected weight scalar transport

## Claim

In the displayed Case 2 selected-entry chart, the common selected variable
`u` in `D_J = u N` is absorbed into the transported row weights
`b'_i = u b_i`.  The corrected finite `Q/P` identity is therefore

```text
(P diag(b) (u N)) (Q C')
  = diag(u b) D''' C'.
```

There is no additional final factor of `u`.

## Lean Names

```text
weightedPivotDiagonal_mul_smul
weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ
```

## Source

Aoyagi PDF pp. 19-21, Case 2.

## Boundaries

Pure finite matrix algebra only.  No chart coverage, source production,
successor chart family, residual-index equivalence, Jacobian/density theorem,
normal-crossing production, pole order, or RLCT extraction.
