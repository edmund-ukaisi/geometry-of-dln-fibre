# Statement card - A4 normalized pivot step

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `be15751`.

Names:

- `DLNFibre.DLN.Aoyagi.pivotPostQBlock_eq_weightedPivotBlockMatrix`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul`

## Statement

In a normalized pivot block

```text
D' = [ 1  y
      x  D ],
```

with diagonal weights `diag(b0,b)` and quotient witnesses `b_i=q_i*b0`, Lean
proves the combined local identity

```text
P * diag(b0,b) * (D' * Q)
  = diag(b0,b) * [ 1 0
                   0 D - x*y ].
```

It also proves the algebraic corollary with the following factor multiplied by
`Q^-1`:

```text
(P * diag(b0,b) * D') * C
  = (diag(b0,b) * [ 1 0
                    0 D - x*y ]) * (Q^-1 * C).
```

The theorem is over a `CommRing`; no division by the monomial weights,
determinant chart, analytic input, or RLCT input is used.

## Source role

This packages the displayed local `Q` and `P` matrix identities on Aoyagi PDF
pp. 17-21 after the pivot entry has been normalized to `1`. It applies to the
displayed pivot branches of Case 1(2) and Case 2, conditional on already being
in that normalized pivot chart and having quotient witnesses for the weights.

This is independent of the Case 2 printed-vector mismatch.

## Proved

- The post-`Q` block has exactly the block shape required by the `P` theorem.
- The `Q` operation changes the lower-right block to `D - x*y`.
- The weighted `P` row operation then clears the lower pivot column.
- The following-factor version is an algebraic product identity with the factor
  multiplied by `Q^-1`.

## Not proved

- No construction of the pivot chart or proof that the pivot entry can be
  normalized to `1`.
- No proof that all pivot charts are covered.
- No proof that the `Q` or `P` substitutions are regular polynomial coordinate
  changes with unit Jacobian, or that they preserve analytic ideal germs.
- No construction of quotient witnesses from polynomial coordinates beyond the
  separate monomial recurrence divisibility theorem.
- No connection yet to monomial/exponent updates.
- No full Case 1/2 transition invariant, termination proof, normal-crossing
  certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh statement-shape reviewed at `be15751`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom`
- `git diff --check`
