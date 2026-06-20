# Review - A4 Case 2 terminal-last actual-width boundary

Reviewed objects:

- `matrixEntryIdeal_mul_ndrec_one`
- `matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast`
- `exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `sourceChart_actualWidth_terminalLastOriginalRowsBoundary`
- `reproduction-case2-terminal-last-actual-width-a4.md`
- `statement-card-a4-case2-terminal-last-actual-width.md`

Verdict: no blocking source/math or Lean API issue found.

The terminal-last suffix removal is routed through the raw source-suffix
identity `sourceSuffixProduct_terminalLast_eq_cast_one` and the endpoint helper
`sourceLayerIndex_terminalLast`, then consumed at the matrix-entry-ideal level
by `matrixEntryIdeal_mul_ndrec_one`.  This avoids pretending that the lower
suffix endpoint and final endpoint are definitionally equal.

The actual-width original-row branch keeps `n(S+1)=J+1` explicit, and the
terminal-last wrapper keeps `S+1=L` explicit.  The row-exhausted wide-next
branch is not conflated with this theorem.

The docs keep the result scoped: this consumes the raw source suffix in the
terminal-last actual-width branch, but does not prove chart coverage, source
production of `C'^(S+1)`, chart-produced following products, Jacobian
arithmetic, normal crossings/RLCT extraction, termination, transition
invariance, or repair of the printed Case 2 vector mismatch.

The adjacent ledger/thread entries now include the actual-width terminal-last
wrapper, but top-level summaries still needed stale empty-suffix/next-target
wording cleaned up.
