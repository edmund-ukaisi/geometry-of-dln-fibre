# Statement card - A4 Case 2 displayed cleared-block following-factor absorption

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.weightedPivotClearedBlock_zero_mul_verticalBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont`

## Statement

Lean proves the generic block multiplication identity

```text
weightedPivotClearedBlock 0 * verticalBlock Ctop Ctail
  = verticalBlock Ctop 0.
```

It also specializes this to the displayed Case 2 cleared block: under displayed
pivot validity and failed next continuation, the already-cleared block
`weightedPivotClearedBlock (D - x*y)` has the same product with any
pivot-first following factor.

## Proved

- A pivot-only cleared block keeps the top following-factor row and kills the
  lower following-factor block.
- The displayed Case 2 cleared block has this behavior when the next
  continuation bound fails.

## Assumed

- The displayed pivot and failed next-continuation hypotheses for the Case 2
  specialization.
- The failed next-continuation hypothesis is the old-coordinate post-pivot
  condition `not (J+2 <= prefixMinNat n (S+1))`.
- The following factor is already split as `verticalBlock Ctop Ctail` in
  pivot-first coordinates.

## Not Proved

- No construction or identification of Aoyagi's `C'^(S+1)`.
- No full source `D'''_J` terminal branch, row-vs-column presentation,
  `S+1` recurrence/exponent state, chart production, chart coverage,
  coordinate regularity, Jacobian/volume arithmetic, normal crossings, RLCT
  extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-cleared-block-following-factor-a4.md`.
- Review artifact:
  `review-case2-displayed-cleared-block-following-factor-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
