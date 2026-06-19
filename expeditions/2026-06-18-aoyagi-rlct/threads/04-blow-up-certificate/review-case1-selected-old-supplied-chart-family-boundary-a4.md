# Review - A4 Case 1 selected-old supplied chart-family boundary

Status: reviewed by controller and independent xhigh reviewer; pass.

## Math Review

The package is a supplied interface, not a chart-production theorem. It
combines:

- `Case1DisplayedRowStripSelectedOldPullbackBoundary`, which supplies the
  selected-old pullback and displayed row-strip local handoff;
- `Case1CenterChartFamilyBoundary`, which supplies chart regularity and
  transition regularity for every generator in the finite Case 1 center.

The source-label facts still come from the pullback boundary, not from the
`Unit` token. The displayed-pivot chart facts use first-jump positivity and
the source column bound to prove finite center membership before projecting
supplied regularity.

## Lean/API Review

The name includes `SuppliedChartFamilyBoundary` to keep the assumption status
visible. The projection theorems do not prove regularity or chart coverage;
they expose the supplied regularity and transition-regularity predicates at
the selected old token and displayed top-left row-strip pivot.

The package also re-exports the existing selected-old source step, displayed
source-order identity, and exponent-domain extension from the pullback
boundary.

## Caveats

- This does not construct the selected-old chart.
- This does not prove an affine atlas, chart coverage, or chart regularity.
- This does not construct the source pullback from raw coordinates.
- This does not prove chart-produced post-data, Jacobians, normal crossings,
  or RLCT extraction.

## Independent xhigh Review

The independent xhigh reviewer found no blocking, major, or minor
formalisation/math findings. The review confirmed that the Lean package is
honest about being a supplied interface; that the `Unit` center token remains
separate from the selected old source label `(s0,k0)`; that displayed-pivot
membership uses first-jump positivity and the actual source column bound; and
that the docs avoid claiming chart production, coverage, Jacobians, normal
crossings, or RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
