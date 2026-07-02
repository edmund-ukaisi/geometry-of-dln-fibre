# Review - A2 with-following inverse-Haar original-volume readback density socket

Date: 2026-07-02.

Reviewer: xhigh explorer `Meitner the 2nd`.

## Result

No findings.

## Checked

- The exact raw-pushforward equality remains an explicit theorem hypothesis.
- The theorem preserves the same local shrink and source-image hypotheses from
  the inverse-Haar bridge.
- The proof consumes the prior inverse-Haar source-image bridge and the generic
  original-volume `withDensity` readback socket.
- The theorem is not a duplicate of the older readback-only wrappers because
  it returns the exact `withDensity` identity and the a.e. inverse-Haar density
  bound together with readback domination.
- The reproduction and statement card do not claim raw transport,
  source-prior/original-prior transport, source-image coverage beyond the local
  chart, normal crossings, pole order, or RLCT extraction.

## Residual risk

The reviewer did not rerun Lean.  Controller verification reran the focused
module build, full `DLNFibre` build, no-sorry audit, whitespace check, touched
Lean-file marker scan, and direct axiom probe.
