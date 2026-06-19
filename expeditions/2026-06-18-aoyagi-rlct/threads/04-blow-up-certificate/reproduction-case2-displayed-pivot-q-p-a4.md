# A4 Case 2 Displayed Pivot `Q/P` Instantiation

Status: checked finite algebra reproduction for the source-displayed top-left
Case 2 chart only.

## Scope

This note isolates the part of Aoyagi Case 2 that is actually displayed in the
paper: the pivot chart selecting `d_(J+1,J+1)` in the residual block. It does
not treat arbitrary selected residual-block pivots as source-reproduced. Those
remain conditional scaffolding until a chart-atlas or row/column permutation
argument is supplied.

The source text is Aoyagi PDF pp. 19-21. The corrected width convention used
by the expedition remains:

```text
row range:    J+1 <= i <= mu_S = M(S)
column range: J+1 <= j <= n_(S+1) = M^(S+1).
```

The prefix-minimum corrected exponent vector is separate from this local
matrix algebra and is not presented as the PDF's printed vector.

## Source Reproduction

Case 2 assumes flat row weights:

```text
b_(J+1) = ... = b_(M(S)).
```

It blows up the full residual-block center

```text
d_ij = 0,
J+1 <= i <= M(S),
J+1 <= j <= M^(S+1),
```

and displays the chart where the selected entry is `d_(J+1,J+1)`. In that
chart the residual block is written as the selected variable times a
normalised block:

```text
D_J = u_(S,J+1) *
      [ 1  y
        x  A ],
```

where the top-left pivot entry is `1`. The following factor is changed by the
displayed inverse `Q^{-1}`, i.e. `C' = Q^{-1} C`, and the displayed `P` matrix
uses quotients of row weights. Since the Case 2 row weights are flat, after the
common selected variable is included,

```text
u * b_i = u * b_(J+1)
```

for every residual row. Thus the quotient witnesses can be chosen trivially.

The local product identity is therefore a direct instance of the already
proved pivot-first `Q/P` algebra:

```text
(P * diag(u*b_(J+1), u*b_i) * A_pivot_first) * C
  =
(diag(u*b_(J+1), u*b_i) * [1 0; 0 D_next]) * (Q^{-1} C).
```

## Lean Shape

Lean names the finite residual row and column index types:

```text
Case2ResidualRowIndex n S J
Case2ResidualColIndex n S J
```

Under the continuation bound `J+1 <= mu_(S+1)`, the displayed pivot row and
column are:

```text
case2DisplayedPivotRow n hS hcont
case2DisplayedPivotCol n hS hcont
```

The selected-entry substitution is split into:

```text
selectedEntrySubstitutionMatrix = u * selectedEntryNormalizedMatrix,
selectedEntryNormalizedMatrix pivot pivot = 1.
```

The theorem `exists_case2DisplayedQP_mul_of_flat_weights` applies the existing
existential pivot-first `Q/P` wrapper to this normalised matrix. It assumes
the flat row-weight hypothesis in the displayed residual-row coordinates and
chooses the quotient witnesses internally.

## What Is Not Reproduced

- No arbitrary selected residual-block pivot chart is source-reproduced.
- No affine blow-up atlas or chart coverage theorem is proved.
- No row/column permutation argument is supplied.
- No general coordinate transport theorem is proved beyond the following
  factor already being in pivot-first coordinates in the theorem statement.
- No exponent update or corrected-vector transition theorem is proved.
- No termination, normal-crossing certificate, or RLCT extraction is included.

## Kill Conditions

- If `J+1` is not in the residual row or column range, the displayed pivot
  index is invalid.
- If the selected-entry substitution has not been factored to a normalised
  pivot entry `1`, the pivot-first `Q/P` theorem does not apply.
- If row weights are not flat in the displayed residual-row coordinates, the
  trivial quotient witness argument fails.
- If an arbitrary pivot is used, quotients must be stated relative to that
  pivot row and a separate chart-atlas or permutation argument is required.
- If the corrected prefix-minimum vector is treated as the source-printed Case
  2 vector, the statement overclaims source fidelity.
