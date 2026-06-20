# Statement card - A4 principalized terminal-last boundaries

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`

## Statement

Lean now packages the terminal-last Case 2 source-chart terminal boundaries
with finite residual-block center principalization.

## Proved

- In both branches, the displayed source chart's selected variable belongs to
  the transformed finite center value set.
- In both branches, every transformed finite center value is divisible by the
  selected variable.
- In both branches, the transformed finite center ideal is `Ideal.span {u}`.
- In the actual-width branch, under `n(S+1)=J+1` and `S+1=L`, the terminal
  product uses original source rows and the relabelled `(S+1,0)` certificates.
- In the row-exhausted branch, under `prefixMinNat n S=J+1` and `S+1=L`, the
  terminal product uses transported prefix rows.

## Assumed

- The displayed Case 2 stage and continuation hypotheses.
- The residual-block chart-family regularity and transition interface.
- The pre-state exponent certificate, level invariant, and least-value gap.
- Supplied source following data `C` and edge matrices `Ctail`.
- Actual-width exhaustion for the original-row branch.
- Current-prefix row exhaustion for the transported-prefix branch.

## Cited

- None in Lean.  This is finite algebra and bookkeeping.

## Deferred

- Terminal-product principalization.
- Chart coverage and affine-atlas construction.
- Source production of `C'^(S+1)` and of the following product.
- Row-exhausted original-row equality or `(S+1,0)` relabelled certificates.
- Jacobian/volume arithmetic, normal crossings, RLCT extraction, termination,
  transition invariance, and repair of the printed Case 2 vector mismatch.

## Review

- Review artifact:
  `review-case2-principalized-terminal-last-boundaries-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
