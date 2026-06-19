# Statement card - A4 normalized P row operation

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockMatrix`
- `DLNFibre.DLN.Aoyagi.weightedPivotClearedBlock`
- `DLNFibre.DLN.Aoyagi.weightedPivotDiagonal`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_mul_diagonal_mul`

## Statement

In a normalized pivot block indexed as `Unit ⊕ lower`, with

```text
D'' = [ 1  0
       x  D ],
```

diagonal weights `diag(b0,b)`, and quotient witnesses `b_i=q_i*b0`, define

```text
P = [ 1  0
     -q_i*x_i  I ].
```

Lean proves:

```text
P * diag(b0,b) * D'' = diag(b0,b) * [ 1  0
                                      0  D ].
```

The theorem is over a `CommRing`; it uses no division, no invertibility of
`b0`, and no analytic/RLCT input.

## Source role

This is the normalized row-operation algebra behind the displayed `P` matrices
on Aoyagi PDF pp. 17-21.  It applies to both Case 1(2) and Case 2 after the
`Q` operation has made the pivot row `(1,0,...,0)`.

Independent xhigh scout `Gauss the 2nd` checked the pen-and-paper algebra and
confirmed that the proof is independent of the Case 2 vector typo.

## Proved

- The first lower-column entries are cleared by the quotient witnesses.
- The lower-right block is unchanged because the pivot row has zero off the
  pivot.
- The top row is unchanged.

## Not proved

- No construction of the quotient witnesses from the monomial recurrence. That
  is supplied separately by the monomial recurrence divisibility card.
- No proof that all pivot charts are covered.
- No proof of the surrounding `Q` operation.
- No full Case 1/2 transition invariant, termination proof, normal-crossing
  certificate, or RLCT extraction.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
