# Statement card - A4 Case 1 selected-old source-coordinate wrapper

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`1e3fd683828792156263d89064f1407624eb79b9`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_selectedEntryChartMap_value_mem`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_center_dvd`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates`

## Statement

Lean now adapts the already supplied displayed Case 1(2) selected-old boundary
to source-coordinate residual and following-factor functions. The new
source-coordinate theorem restricts `Nat x Nat -> R` residual data to the
active residual block, restricts `Nat -> tau -> R` following-factor data to
the residual columns, and then invokes the existing displayed source-order
identity.

The same checkpoint projects finite selected-entry principalization facts for
the displayed top-left row-strip pivot.

## Source Role

This matches Aoyagi PDF pp. 15-19 for the displayed Case 1(2) chart: the
selected old variable is factored by the new pivot variable, the row-strip
pivot is normalized to `1`, and the following factor is transformed by
`Q^-1`. The theorem is a source-coordinate adapter for that displayed chart,
not chart production.

## Proved

- Source residual and following-factor functions feed into the existing
  displayed Case 1(2) source-order identity.
- The displayed top-left row-strip chart token has finite center
  principalization projections to `(u)`.
- The selected variable occurs in the transformed finite center value set for
  the displayed top-left row-strip chart token.
- Every transformed finite Case 1 center generator is divisible by the selected
  variable in the displayed top-left row-strip chart token.

## Assumed

- Supplied selected-old pullback/local handoff data.
- Supplied Case 1 finite chart-family regularity and transition regularity.
- Supplied source-coordinate residual and following-factor functions.
- Supplied displayed pivot normalization `residual(J+1,J+1)=1`.

## Not Proved

- No construction of a blow-up chart or affine atlas.
- No proof that the `Unit` center token itself determines `(s0,k0)`.
- No selected-old `Unit` principalization projection using the displayed
  pivot variable `u`.
- No construction of the raw-coordinate-to-`source` pullback.
- No proof of chart-produced post-data, chart coverage, regularity,
  transition regularity, or Jacobian formula from coordinates.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-source-coordinate-wrapper-a4.md`.
- Review artifact:
  `review-case1-selected-old-source-coordinate-wrapper-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
