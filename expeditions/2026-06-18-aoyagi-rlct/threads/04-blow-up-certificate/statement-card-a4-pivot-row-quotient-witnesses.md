# Statement card - A4 pivot-row quotient witnesses

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `c81d19f`.

Names:

- `DLNFibre.DLN.Aoyagi.exists_right_quotients_of_forall_dvd`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_of_forall_eq`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_of_forall_eq_or_dvd`
- `DLNFibre.DLN.Aoyagi.monomialRec_tail_eq_right_mul`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_monomialRec_of_le`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_monomialRec_of_eq_or_le`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_pivotMul_monomialRec_of_le`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_pivotMul_monomialRec_of_eq_or_le`
- `DLNFibre.DLN.Aoyagi.exists_right_quotients_const`
- `DLNFibre.DLN.Aoyagi.exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd`

## Statement

Lean proves generic quotient-witness infrastructure for the `P` row operation.
If every lower-row weight is divisible by the pivot-row weight, Lean chooses a
function `q` such that every lower-row weight is `q i * b0`, the exact
hypothesis shape used by `weightedPivotBlockRowOp_mul_diagonal_mul`.

The monomial recurrence wrappers show that later recurrence terms admit these
right-oriented quotient witnesses over an earlier term, and that common
multiplication by a pivot variable preserves the witnesses. The
equality-or-later wrappers cover the Case 1 formalisation shape where rows in
the flat strip have equal weight and later rows are handled by the recurrence.

## Source role

Aoyagi's displayed `P` matrices use quotients `b'_i / b'_pivot`. For the
displayed top-left pivot, the recurrence and the Case 1/Case 2 flat-weight
hypotheses explain why these quotients are monomials. For non-displayed matrix
pivots, this remains a conditional formalisation scaffold: selected-entry
charts, pivot normalisation, coordinate transport, pivot-first weight transport,
and Aoyagi-specific row-weight hypotheses must be proved separately.

## Proved

- Divisibility/equality hypotheses produce right-oriented quotient witnesses.
- Later `monomialRec` terms have quotient witnesses over an earlier term.
- Equal-or-later recurrence terms have quotient witnesses over the pivot term.
- Multiplying all relevant weights by a common pivot variable preserves those
  quotient witnesses.
- Divisibility of lower-row weights supplies an existential `P` row-operation
  identity via the existing normalised matrix theorem.

## Assumed

- The row weights are already the weights in the chosen pivot-first coordinates.
- For the `P` bridge, every lower-row weight is assumed divisible by the pivot
  row weight, or this is supplied by one of the monomial/equality wrappers.

## Not proved

- No selected-entry chart construction, coordinate transport, affine atlas, or
  chart coverage.
- No proof that arbitrary Aoyagi pivot rows satisfy the equality-or-later
  hypotheses.
- No Case 1 or Case 2 transition invariant.
- No regularity/Jacobian theorem, exponent update, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-pivot-row-weight-quotients-a4.md`.
- Xhigh source/Lean review confirmed the Lean statements are generic algebra
  and that the arbitrary-pivot reading must remain conditional.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
