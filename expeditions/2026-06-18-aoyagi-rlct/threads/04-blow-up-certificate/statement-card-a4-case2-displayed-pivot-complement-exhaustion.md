# Statement card - A4 Case 2 displayed pivot-complement exhaustion

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivPostPivotRows`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivPostPivotRows_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivPostPivotRows_symm_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivPostPivotCols`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivPostPivotCols_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivPostPivotCols_symm_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplement_isEmpty_iff_postPivotRows_isEmpty`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplement_isEmpty_iff_postPivotCols_isEmpty`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplement_isEmpty_of_postPivotRows_eq_empty`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplement_isEmpty_of_postPivotCols_eq_empty`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotComplement_isEmpty_or_isEmpty_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont`

## Statement

Lean identifies the displayed pivot-complement row type with the old
post-pivot row range `J+2..M(S)`, and the displayed pivot-complement column
type with the old post-pivot column range `J+2..M^(S+1)`.

If the displayed pivot is valid but the next continuation bound fails, then
one of those two pivot-complement types is empty:

```text
not (J+2 <= prefixMinNat n (S+1))
  => IsEmpty rowComplement or IsEmpty colComplement.
```

As a downstream API corollary, every lower-right matrix indexed by these two
complement types is equal to every other; over a type with zero, such a matrix
is equal to `0`.

## Source Role

This is the finite index content behind Aoyagi's PDF pp. 21-22 terminal
paragraph after the displayed Case 2 `Q/P` calculation.  It supports the
eventual terminal `D'''` block-shape proof, but does not prove that theorem.

## Proved

- Displayed pivot row complement is equivalent to the finite subtype of
  `case2PostPivotRows`.
- Displayed pivot column complement is equivalent to the finite subtype of
  `case2PostPivotCols`.
- Empty post-pivot row/column finsets imply empty displayed pivot-complement
  row/column types.
- Failure of the next continuation bound empties at least one displayed
  pivot-complement type.
- Under the same failure, the lower-right complement matrix type is
  subsingleton, and each such matrix is zero when the codomain has `Zero`.

## Assumed

- `1 <= S`, needed for the prefix-minimum successor convention used by the
  preceding post-pivot exhaustion lemmas.
- `J+1 <= prefixMinNat n (S+1)`, the displayed pivot-validity hypothesis.

## Not Proved

- No construction of Aoyagi's `D'''_J`.
- No theorem that `D'''_J = (1,0,...,0)` or its transpose.
- No post-`Q/P` whole-block zero-pattern theorem.
- No `S+1` recurrence/exponent state, following-factor absorption, chart
  production, chart coverage, coordinate regularity, Jacobian/volume
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-pivot-complement-exhaustion-a4.md`.
- Review artifact:
  `review-case2-displayed-pivot-complement-exhaustion-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
