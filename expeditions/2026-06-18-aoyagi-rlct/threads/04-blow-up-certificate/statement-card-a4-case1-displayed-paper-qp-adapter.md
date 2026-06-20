# Statement card - A4 Case 1 displayed paper `Q/P` adapter

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDchart`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDchart_pivot`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperSourceBlock`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperQ`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperQinv`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDpp`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperCprime`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDppp`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDpp_eq_pivotPostQBlock`
- `DLNFibre.DLN.Aoyagi.case1DisplayedPaperDpp_mul_Cprime`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates_paperQP`

## Statement

Lean now exposes paper-facing names for Aoyagi's displayed Case 1(2) top-left
`Q/P` calculation. The checkpoint names the already supplied
source-coordinate residual block, the row-strip source block, `Q`, `Q^-1`,
`D''`, `C'`, and `D'''`, then restates the existing source-order identity in
this notation.

## Source Role

This matches Aoyagi PDF pp. 16-18. The displayed chart normalizes the
top-left row-strip pivot by `d'_(J+1,J+1)=1`, uses the column operation
`Q`, transports the following factor by `C' = Q^-1 C`, and applies a
row operation `P` to obtain the cleared block `D'''`.

`Dchart` is an internal Lean name for the normalized pre-`Q` residual block;
Aoyagi does not separately name it `D_chart`.

## Proved

- The source-coordinate displayed pivot value is exactly
  `residual (J+1,J+1)`.
- The paper block `D''` is the generic post-`Q` block under the supplied
  normalization `residual (J+1,J+1)=1`.
- The orientation `C' = Q^-1 C` is pinned by
  `D'' * C' = D_chart^pivot * C`.
- The supplied displayed source-order identity is available in paper notation:
  `P * diag(source weights) * source block * C =
   diag(post weights) * D''' * C'`.

## Assumed

- The normalized displayed source-coordinate block and pivot normalization.
- The selected-old pullback/local handoff boundary.
- Supplied recurrence/exponent post-data and quotient witnesses from earlier
  boundaries.
- Supplied chart-family regularity and transition regularity predicates.

## Not Proved

- No construction of a blow-up chart or affine atlas.
- No proof that the `Unit` token identifies `(s0,k0)`.
- No construction of source recurrence states or exponent post-data from raw
  coordinates.
- No chart coverage, regularity from coordinates, transition formula, or
  Jacobian accounting.
- No arbitrary-pivot coverage, normal crossings, RLCT extraction, or full
  transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-paper-qp-adapter-a4.md`.
- Review artifact:
  `review-case1-displayed-paper-qp-adapter-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
