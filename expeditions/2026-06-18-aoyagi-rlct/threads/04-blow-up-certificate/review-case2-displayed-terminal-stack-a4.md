# Review - A4 Case 2 Displayed Terminal Stack

## Reviewers

- Source/math reviewer: `Locke the 4th`, xhigh.
- Lean/API reviewer: `Gauss the 4th`, xhigh.

## Findings

No high- or medium-severity issue was found.

The Lean/API reviewer found no API issue.  The generic stacking lemmas
`matrixEntryIdeal_sumElim_eq_sup` and
`matrixEntryIdeal_sumElim_congr_bottom` are appropriately general and require
no unnecessary `Fintype` hypotheses.  The displayed terminal stack theorem is
a direct adapter over the prior stopped-tail theorem.

The source/math reviewer confirmed that the result is correct finite
entry-ideal algebra and safe only as source-order-shaped scaffolding, not as
Aoyagi's full terminal transition.  One caveat was sharpened after review:
the theorem stacks raw `D''' * C'` against raw `C0` over a supplied `Cold`;
it is not the diagonal-weighted full terminal product ideal from Aoyagi
PDF pp. 21-22.

## Verification

Focused reviewer checks:

- `lake build DLNFibre.DLN.Aoyagi.EntryIdeal`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `git diff --check 6689dfb`

Controller full gates are recorded in the checkpoint commit.

## Residual Risk

This checkpoint does not identify `Cold` with the source old top rows or
`[Cold;C0]` with Aoyagi's full `C'^(S+1)`. It also does not prove the
diagonal-weighted full terminal product ideal, choose the row-vs-column
terminal presentation, build `S+1` post-data, prove chart coverage or
regularity, compute Jacobians, prove normal crossings, extract RLCT, prove
termination or transition invariance, or repair the printed vector mismatch.
