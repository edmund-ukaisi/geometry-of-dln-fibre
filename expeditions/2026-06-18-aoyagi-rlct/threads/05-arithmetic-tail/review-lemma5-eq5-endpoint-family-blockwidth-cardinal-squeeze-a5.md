# Review - Lemma 5 Eq5 endpoint-family block-width cardinal squeeze

Date: 2026-06-22.

Reviewer: Copernicus, xhigh-effort subagent.

## Verdict

Pass.

## Findings

No blocking formal or source-boundary issues were found.  The Lean wrappers are
honest: they only convert the blockwise actual-width hypothesis into the
existing per-label width bound via
`cut.selectedWidthNat_le_actualWidth_of_block`, then call the existing
endpoint-family squeeze.

The docs frame the result as supplied finite bookkeeping and defer
source-backed no-extra coverage, branch construction, terminal payload
production, order count, pole order, normal crossings, and RLCT extraction.

## Residual Risk

This is worth keeping only as a thin convenience wrapper.  It is compatible
with the A5 freeze recommendation because it does not claim source progress,
but it should not justify more A5 wrapper work; the source audit recommends
pivoting back to the A4 source-production frontier.
