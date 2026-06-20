# Statement card - A4 Case 2 post-pivot domain handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2PostPivotRows_eq_case2ResidualBlockRows_succ`
- `DLNFibre.DLN.Aoyagi.case2PostPivotCols_eq_case2ResidualBlockCols_succ`
- `DLNFibre.DLN.Aoyagi.case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivResidualRowSucc`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivResidualColSucc`

## Statement

Lean now records that after deleting Aoyagi's displayed Case 2 pivot
`(J+1,J+1)`, the lower-right row, column, and entry domains are exactly the
next same-stage residual-center domains for `(S,J+1)`.

The next residual center is nonempty exactly when the next continuation bound
holds:

```text
J+2 <= prefixMinNat n (S+1).
```

## Proved

- Post-pivot rows `J+2..M(S)` equal `case2ResidualBlockRows n S (J+1)`.
- Post-pivot columns `J+2..M^(S+1)` equal
  `case2ResidualBlockCols n S (J+1)`.
- Post-pivot entries equal `case2ResidualBlockPivotEntries n S (J+1)`.
- Deleting the displayed pivot row/column gives equivalences to the next
  residual row/column index types.
- The next same-stage residual center is nonempty iff the next continuation
  bound holds.

## Assumed

- `1 <= S` only for the nonemptiness theorem, where Lean uses
  `prefixMinNat n (S+1) = min (prefixMinNat n S) (n(S+1))`.
- The pivot-complement equivalences also carry `1 <= S` and the current
  continuation hypothesis `J+1 <= prefixMinNat n (S+1)`, because their source
  subtypes are defined from the displayed current pivot.
- The displayed Case 2 domain conventions already present in
  `BlowupArithmetic.lean`.

## Cited

- None in Lean.  This is finite domain bookkeeping.

## Deferred

- Source production of the next residual matrix or `C'^(S+1)`.
- Chart coverage, transition invariance, transition regularity, Jacobian
  arithmetic, terminal-product principalization, normal crossings, RLCT
  extraction, and repair of the printed Case 2 vector mismatch.
- The terminal `(S+1,0)` relabel branch.

## Review

- Reproduction checked by xhigh `Hubble the 5th`.
- Landed-patch review passed by xhigh `Dirac the 5th`; one documentation note
  on the complement-equivalence hypotheses was incorporated.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
