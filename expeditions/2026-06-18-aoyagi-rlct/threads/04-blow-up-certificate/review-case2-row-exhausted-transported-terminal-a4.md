# Review - A4 Case 2 row-exhausted transported terminal

Status: passed xhigh source/math and Lean/API exploration, and
post-implementation Lean/source-fidelity review.

## Source/Math Review

No blocking source/math issue was found in the row-exhausted branch.

- The terminal object is the terminal-prefix `C'`, indexed by `1..M(S+1)`.
- Under current-prefix row exhaustion and displayed continuation, this is
  equivalent to source rows `1..J+1`.
- Rows `1..J` are unchanged old source rows.
- Row `J+1` is the top row of `Q^-1 C`, not generally the original source
  row.
- In a row-exhausted wide-next branch, the post-pivot actual columns may be
  nonempty, so the correction sum in `case2DisplayedPaperCprimeTop_apply` is
  genuine.

## Lean/API Review

No blocking Lean/API issue was found in the proposed shape.

- `case2_not_next_cont_of_prefixMin_current_eq` is the finite arithmetic
  bridge from current-prefix row exhaustion to stopped continuation.
- `case2DisplayedSourceTerminalTransportedRows` makes the transported pivot
  row explicit.
- `SuppliedTerminalCprimeBridge.of_transportedRows` is a formula-level bridge,
  not a chart-production theorem.
- The row-exhausted source-suffix wrappers should consume the existing
  terminal-prefix product theorem and supplied-bridge consumer.

## Residual Risk

This checkpoint does not certify chart coverage or the RLCT pipeline.  It also
does not justify recurrence/exponent relabelling to `(S+1,0)`; that remains
an actual-width-only result.

## Post-Implementation Review

No blocking issue was found.

- The Lean path derives failed next continuation from current-prefix row
  exhaustion.
- It reuses terminal-prefix row indexing.
- It exposes transported terminal rows.
- It does not claim actual next-width exhaustion, original-row equality,
  `(S+1,0)` relabelling, chart production, normal crossings, or RLCT.

Verification reported by reviewer:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```
