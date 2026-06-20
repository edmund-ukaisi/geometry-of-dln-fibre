# Review - A4 Case 2 post-pivot next block

Reviewer: `Ptolemy the 5th` (xhigh pen-and-paper/source check).

Verdict: pass for a supplied-data adapter target.

## Scope Checked

- Aoyagi PDF pp. 19-22.
- Proposed target shape for the continuing displayed Case 2 branch.
- Existing post-pivot domain handoff and displayed `D'''`, `C' = Q^-1 C`
  notation.

## Findings

No source-level blockers for the narrow adapter.

The source supports packaging the lower-right cleared block `D - x*y` and the
tail of the transported following factor `Q^-1 C` as supplied data over the
next same-stage domains `(S,J+1)`.  The adapter is independent of the printed
Case 2 exponent-vector mismatch because it makes no exponent-vector,
numerator, Jacobian, normal-crossing, or RLCT claim.

The reviewer emphasized that this is not a chart-produced transition theorem.
The continuing branch should expose the bound
`J+2 <= prefixMinNat n (S+1)` when nonemptiness is claimed.

## Lean API Scout

Reviewer: `Noether the 5th` (xhigh Lean API scout).

Verdict: pass for definitions plus a small product-shape theorem.

Suggested names were the `case2DisplayedPostPivot...` family now used in Lean.
The review warned against using terminal/source suffix wrappers for this
target and against names that suggest source-produced `C'^(S+1)`.

## Landed-patch review

Reviewer: `Plato` (xhigh landed-patch review).

Verdict: pass.

No issues were found.  The reviewer checked that the residual block is the
cleared lower-right `D - x*y`, reindexed to next same-stage domains; that the
following factor is the tail of `C' = Q^-1 C`; that the next column domain is
same-stage actual-width `Case2ResidualColIndex n S (J+1)` rather than a
prefix-width column domain; and that the continuing nonempty condition
`J+2 <= prefixMinNat n (S+1)` appears only where nonemptiness is claimed.

Verification passed for the reviewer:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
git diff --check
```

Residual risk: later consumers must not treat this adapter as chart
production, recurrence/exponent post-data from coordinates, transition
invariance, terminal relabeling, or normal-crossing/RLCT evidence.
