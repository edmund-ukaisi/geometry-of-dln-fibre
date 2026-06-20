# Review - A4 Case 2 Displayed Paper Terminal Absorption

## Reviewers

- Source/math reviewer: `Halley the 4th`, xhigh.
- Lean/API reviewer: `Averroes the 4th`, xhigh.

## Findings

No source-fidelity, math, Lean/API, or overclaiming issue was found.

The source/math reviewer checked that the paper-notation adapter matches the
displayed Case 2 calculation:

```text
Q = [1 -y; 0 I],    Q^-1 = [1 y; 0 I],
D'' = D_chart * Q,  C' = Q^-1 C,
D''' = blockdiag(1, D - x*y).
```

The stopped-continuation theorem is correctly scoped: it assumes the shifted
post-pivot bound

```text
not (J+2 <= prefixMinNat n (S+1)),
```

uses the existing lower-right vacuity theorem, and concludes only equality of
matrix-entry ideals after zero lower rows are dropped.

The Lean/API reviewer checked that
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap_paperQP`
is a direct adapter over the existing displayed boundary API, and that
`matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont`
composes with the new zero-bottom ideal lemma.

## Verification

Focused reviewer checks:

- `lake env lean DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`

Controller full gates are recorded in the checkpoint commit.

## Residual Risk

This checkpoint is finite algebra and paper notation only.  It does not
construct or identify Aoyagi's next-stage `C'^(S+1)`, choose the row-vs-column
terminal presentation, prove arbitrary-pivot chart coverage, prove chart
production or regularity, derive recurrence/exponent post-data from
coordinates, compute Jacobians, prove normal crossings, extract RLCT, prove
termination, prove transition invariance, or repair the printed Case 2 vector
mismatch.
