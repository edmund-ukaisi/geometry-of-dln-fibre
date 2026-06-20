# Statement card - A4 principalized source-chart actual-width boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`

## Statement

Lean exposes a displayed source-chart actual-width terminal boundary that also
records finite residual-block center principalization.  The terminal
entry-ideal equality keeps the following product as an arbitrary supplied
matrix `F : Matrix tau upsilon R`.

The theorem assumes the displayed Case 2 stage and continuation hypotheses
(`hS`, `hSL`, `hcont`), actual-width exhaustion `n(S+1)=J+1`, pre-state
exponent certificates, level invariants, the least-value gap, and a supplied
residual-block `chartFamily`.

## Proved

- The displayed source chart's selected variable belongs to the transformed
  finite center value set.
- Every transformed finite center value is divisible by the selected variable.
- The transformed finite center ideal is `Ideal.span {u}`.
- Under `n(S+1)=J+1`, the stopped terminal product uses original source rows
  `1..J+1` and the supplied following matrix `F`.
- The actual-width relabelled level invariant and exponent-domain certificate
  are packaged with the entry-ideal equality.

## Assumed

- The residual-block chart-family regularity and transition interface.
- The pre-state exponent certificate, level invariant, and least-value gap.
- The following matrix `F`.

## Cited

- None in Lean.  This is finite algebra and bookkeeping.

## Deferred

- Chart coverage and affine-atlas construction.
- Source production of `C'^(S+1)` and of the following product.
- Jacobian/volume arithmetic, normal crossings, RLCT extraction, termination,
  transition invariance, and repair of the printed Case 2 vector mismatch.

## Review

- Review artifact:
  `review-case2-principalized-source-chart-actual-width-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
