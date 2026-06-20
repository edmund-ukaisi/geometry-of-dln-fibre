# Review - A4 Case 2 Displayed Cleared-Block Following-Factor Absorption

## Reviewers

- Source/math reviewer: `Bacon the 4th`, xhigh.

## Findings

No source-fidelity or overclaim issue was found.  The generic lemma
`weightedPivotClearedBlock_zero_mul_verticalBlock` is exactly the block
multiplication `[1 0; 0 0] * [Ctop; Ctail] = [Ctop; 0]`.  The displayed
specialization first uses the prior lower-right vacuity result and then
applies this generic multiplication lemma.

The reviewer highlighted three caveats, now recorded in the reproduction and
statement card:

- `Ctop` and `Ctail` are already in pivot-first vertical coordinates.
- `hstop` is the old-coordinate post-pivot condition
  `not (J+2 <= prefixMinNat n (S+1))`.
- The conclusion is only `[Ctop;0]`; it does not identify this block with
  Aoyagi's displayed `C'^(S+1)` data or choose the row-vs-column terminal
  presentation.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint proves only pivot-first block multiplication after the
lower-right cleared block is zero.  It does not construct or identify
Aoyagi's `C'^(S+1)`, construct the full `D'''_J` terminal branch, choose the
row/column presentation, build the `S+1` recurrence/exponent state, prove
chart production or coverage, compute Jacobians, prove normal crossings,
extract RLCT, prove termination, prove transition invariance, or repair the
printed Case 2 vector mismatch.
