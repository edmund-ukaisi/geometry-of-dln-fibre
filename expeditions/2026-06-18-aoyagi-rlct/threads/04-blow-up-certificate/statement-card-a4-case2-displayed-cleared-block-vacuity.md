# Statement card - A4 Case 2 displayed cleared-block vacuity

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont`

## Statement

For the displayed Case 2 normalized residual block, if the displayed pivot
`(J+1,J+1)` is valid and the next continuation bound fails, then the
already-cleared pivot block

```text
weightedPivotClearedBlock (D - x*y)
```

equals the pivot-only cleared block

```text
weightedPivotClearedBlock 0.
```

Here `D - x*y` is the lower-right complement block after the displayed
pivot-first `Q` operation.

## Proved

- Under `J+1 <= prefixMinNat n (S+1)` and
  `not (J+2 <= prefixMinNat n (S+1))`, the lower-right complement block in
  the displayed cleared Case 2 block is zero.
- The cleared block is therefore equal to `weightedPivotClearedBlock 0` in
  pivot-first coordinates.

## Assumed

- The displayed pivot validity and failed next-continuation hypotheses.
- The block is already the displayed normalized residual block in pivot-first
  cleared-block form.

## Not Proved

- No construction of the whole `D'''_J` terminal branch in source notation.
- No row-vs-column presentation as `(1,0,...,0)` or transpose.
- No construction of `C'^(S+1)`, `S+1` recurrence/exponent state, chart
  production, chart coverage, coordinate regularity, Jacobian/volume
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-cleared-block-vacuity-a4.md`.
- Review artifact:
  `review-case2-displayed-cleared-block-vacuity-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
