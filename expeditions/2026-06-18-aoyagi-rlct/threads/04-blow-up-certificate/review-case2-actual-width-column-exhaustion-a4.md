# Review - A4 Case 2 actual-width column exhaustion

Status: passed xhigh source/math review and xhigh Lean/API review; focused
Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-actual-width-column-exhaustion-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-column-exhaustion.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplement_isEmpty_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.displayedPivotColComplement_isEmpty`

## Verdict

PASS with caveats.  The theorem is faithful as finite-domain bookkeeping:
under actual next-width exhaustion `n(S+1)=J+1`, the post-pivot column range
`J+2..n(S+1)` is empty, hence the displayed pivot column complement is empty.
The dependency chain is narrow: it composes the existing post-pivot column
exhaustion lemma with the existing equivalence from displayed column
complement to post-pivot columns.

Caveat: this is only the actual-width, column-exhausted side.  It does not
assert row-complement emptiness; `n(S+1)=J+1` does not force
`prefixMinNat n S=J+1`.

## Checks

- Actual next-width exhaustion is used, not prefix exhaustion.
- The result identifies only the column side under actual-width exhaustion.
- No source-produced `C'^(S+1)`, chart production, coverage, Jacobian,
  normal-crossing/RLCT, termination, transition invariant, automatic gap/tail
  transport, or printed-vector repair is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- Source/math reviewer: PASS, no source/math fidelity blocker.
- Lean/API reviewer: PASS with caveats, no blocking Lean/API issue.
