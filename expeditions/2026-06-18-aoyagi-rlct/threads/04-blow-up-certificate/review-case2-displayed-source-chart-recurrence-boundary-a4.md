# Review - A4 Case 2 Displayed Source-Chart Recurrence Boundary

## Pre-Implementation Scouts

- Source/math scout: `McClintock the 4th`, xhigh.
- Lean/API scout: `Hilbert the 4th`, xhigh.

Both scouts recommended a recurrence-only boundary outside
`Case2DisplayedSuppliedChartFamilyBoundary`, avoiding corrected exponent
post-data, chart-family regularity, Jacobian arithmetic, and coverage claims.

## Findings

No source/math fidelity defect or overclaim was found.  The formalized part
matches only Aoyagi's displayed top-left Case 2 chart variable and the
recurrence update `b'_i = u_(S,J+1) b_i` on residual rows.  The Lean boundary
uses `case2DisplayedSourceChartMap` only through its pivot value at
`(J+1,J+1)` and then applies the existing recurrence successor bookkeeping.

No Lean/API soundness defect was found.  The actual-width derivation from
`hS`, `hSL`, and `hcont` is correct, and the residual-row theorem unfolds the
intended old row weight.  The Lean/API reviewer noted one low clarity point:
the post-data theorem is deliberately weak, since the displayed pivot value is
definitionally `u`; it renames the concrete successor variable by the chart
pivot coordinate and does not connect the full displayed chart or residual
data to the successor.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint intentionally uses only the displayed source chart pivot value
to name the recurrence successor variable.  It does not prove that an affine
chart produces all post-data, and it does not touch exponent/Jacobian data,
coverage, normal crossings, RLCT extraction, termination, transition
invariance, or the printed Case 2 vector mismatch.
