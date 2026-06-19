# Statement card - A4 monomial recurrence divisibility

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.monomialRec`
- `DLNFibre.DLN.Aoyagi.monomialTail`
- `DLNFibre.DLN.Aoyagi.monomialRec_add_eq_tail_mul`
- `DLNFibre.DLN.Aoyagi.monomialRec_dvd_of_le`
- `DLNFibre.DLN.Aoyagi.monomialRec_pivot_dvd`
- `DLNFibre.DLN.Aoyagi.mul_left_dvd_mul_left_of_dvd`
- `DLNFibre.DLN.Aoyagi.pivotMul_monomialRec_dvd_of_le`

## Statement

Given a commutative monoid and a monomial recurrence

```text
b_0 = 1,
b_(k+1) = step_k * b_k,
```

Lean proves that any later term is an earlier term times an explicit tail
product.  Consequently, `b_a | b_b` whenever `a <= b`.  It also proves that
common multiplication by a pivot variable preserves this divisibility.

## Source role

This is the elementary arithmetic needed for regularity of the row-operation
matrix `P` in Aoyagi's pivot charts.  The entries of `P` contain
`b'_i / b'_(J+1)`, so a formal chart certificate must know that
`b'_(J+1)` divides `b'_i`.

Independent xhigh pen-and-paper scout `McClintock the 2nd` confirmed this
reduction.  The scout also confirmed that the displayed `b'_i`/standalone-`u`
source ambiguity must be handled by a consistent normalization in a later
chart certificate.

## Proved

- `monomialRec step (a+k) = monomialTail step a k * monomialRec step a`.
- `monomialRec step a | monomialRec step b` for `a <= b`.
- `monomialRec step (J+1) | monomialRec step i` for `J+1 <= i`.
- If `a | b`, then `u*a | u*b`.
- Therefore common pivot multiplication preserves the recurrence
  divisibility.

## Not proved

- No polynomial-coordinate regularity theorem.
- No construction of the row-operation matrix `P`.
- No proof of the displayed matrix algebra after applying `P`.
- No pivot-chart coverage, termination, normal-crossing certificate, or RLCT
  extraction.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
