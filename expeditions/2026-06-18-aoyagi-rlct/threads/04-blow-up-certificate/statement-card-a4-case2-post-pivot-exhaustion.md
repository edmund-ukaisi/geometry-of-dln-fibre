# Statement card - A4 Case 2 post-pivot exhaustion boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2PostPivotRows`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols`
- `DLNFibre.DLN.Aoyagi.case2PostPivotEntries`
- `DLNFibre.DLN.Aoyagi.mem_case2PostPivotRows`
- `DLNFibre.DLN.Aoyagi.mem_case2PostPivotCols`
- `DLNFibre.DLN.Aoyagi.mem_case2PostPivotEntries_iff`
- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_card`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols_card`
- `DLNFibre.DLN.Aoyagi.case2PostPivotEntries_card`
- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_nonempty_iff`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols_nonempty_iff`
- `DLNFibre.DLN.Aoyagi.case2PostPivotEntries_nonempty_iff_next_cont`
- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_eq_empty_of_le`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols_eq_empty_of_le`
- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_eq_empty_of_prefixMin_current_eq`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols_eq_empty_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.case2_next_frontier_eq_of_cont_of_not_next`
- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_empty_or_cols_empty_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.case2PostPivotEntries_eq_empty_of_not_next_cont`

## Statement

Lean now names the lower-right finite domain left after Aoyagi's displayed
Case 2 pivot at `(J+1,J+1)`.  In old `(S,J)` notation:

```text
post rows    = J+2..M(S),
post columns = J+2..M^(S+1).
```

The post-pivot entry set is nonempty exactly when the next continuation bound
holds:

```text
case2PostPivotEntries n S J is nonempty
  iff J+2 <= prefixMinNat n (S+1).
```

If that next bound fails, then at least one side is empty and the lower-right
post-pivot entry set is empty.

## Source Role

This is the finite-domain boundary behind Aoyagi's PDF pp. 21-22 distinction
between continuing the Case 2 induction with `J` advanced and leaving the
displayed residual block for the `S+1` step.

## Proved

- Membership and cardinality of the post-pivot row, column, and entry sets.
- Row nonemptiness iff `J+2 <= M(S)`.
- Column nonemptiness iff `J+2 <= M^(S+1)`.
- Entry nonemptiness iff `J+2 <= M(S+1)`.
- If the current displayed pivot is valid but the next pivot is not, then
  `M(S+1)=J+1`.
- Failure of the next continuation bound empties the lower-right entry set.

## Assumed

- Only the finite stage positivity hypothesis `1 <= S` is needed to rewrite
  `M(S+1)` as `min(M(S),M^(S+1))`.

## Not Proved

- No construction of the `S+1` advance state or following factor.
- No chart-produced recurrence or exponent post-data.
- No affine atlas, chart coverage, coordinate regularity, Jacobian/volume
  arithmetic, normal crossings, RLCT extraction, termination, full transition
  invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-post-pivot-exhaustion-a4.md`.
- Review artifact:
  `review-case2-post-pivot-exhaustion-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
