# Statement card - A4 Case 2 displayed center count

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2_continuation_le_prefixMinNat_current`
- `DLNFibre.DLN.Aoyagi.case2_continuation_le_width_next`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockRows_card`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockCols_card`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotEntries_card`
- `DLNFibre.DLN.Aoyagi.correctedCase2NewLabelNumerator`
- `DLNFibre.DLN.Aoyagi.correctedCase2NewLabelNumerator_eq_card_of_bounds`
- `DLNFibre.DLN.Aoyagi.correctedCase2NewLabelNumerator_eq_card_of_cont`

## Statement

Lean now proves the finite coordinate count for Aoyagi's displayed Case 2
residual-block center. The row interval `J+1..M(S)` has cardinality
`M(S)-J`, the actual-width column interval `J+1..M^(S+1)` has cardinality
`M^(S+1)-J`, and the selected residual-block coordinate set has cardinality

```text
(M(S)-J)(M^(S+1)-J).
```

The integer expression
`correctedCase2NewLabelNumerator n S J` names this corrected Case 2 scalar and
is proved equal to the selected-coordinate count under explicit interval
bounds, and under the displayed continuation bound.

## Source Role

This follows Aoyagi's displayed Case 2 residual block on PDF pp. 19-21. It
explains why the corrected Case 2 numerator uses prefix-minimum row count and
actual-width column count.

## Proved

- Continuation gives the current prefix-minimum row bound.
- Continuation gives the next actual-width column bound.
- Cardinalities of the residual row and column intervals.
- Cardinality of the residual-block selected-entry set.
- Equality between the corrected integer numerator expression and this finite
  coordinate count under explicit bounds and under continuation.

## Assumed

- For the continuation corollary: `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.

## Not Proved

- No chart coverage or chart regularity.
- No Jacobian exponent or volume-form calculation.
- No chart-produced recurrence or exponent post-data.
- No normal crossing, RLCT extraction, termination, or transition invariant.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-center-count-a4.md`.
- Review artifact:
  `review-case2-displayed-center-count-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
