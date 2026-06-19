# Review - A4 Case 1 selected-old source-coordinate wrapper

Status: reviewed by controller and independent xhigh reviewer; pass after
scope repair.

## Math Review

The checkpoint adapts the existing displayed Case 1(2)
selected-old/chart-family boundary to source-coordinate residual data. The
only new source-coordinate condition is the displayed pivot normalization

```text
residual(J+1,J+1) = 1.
```

The row and column domains remain separate: residual rows use the prefix
minimum active row range, while residual columns use the actual source width.
The following factor is first restricted to residual columns and then reindexed
into the displayed pivot-first column order.

The finite principalization projections are also only projections for the
displayed top-left pivot. They use existing selected-entry algebra plus the
boundary's displayed-pivot center-membership proof. The selected-old `Unit`
projection is intentionally absent because the displayed Case 1(2) variable
`u` is the new row-strip pivot factor, not an independently produced
selected-old chart variable.

## Lean/API Review

The source-coordinate adapter is a theorem, not a new transition certificate.
It invokes
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity`
with `case2SourceResidualBlock residual` and
`case2DisplayedSourceFollowingFactor`.

The projected ideal statements are deliberately named for the displayed pivot
chart token. They do not mention coverage, atlas construction, or Jacobian
behavior.

## Independent xhigh Review

The first independent xhigh review failed the checkpoint because the original
draft projected selected-old `Unit` principalization with the displayed pivot
variable `u` and because the prose said the wrapper instantiated the supplied
boundary. The selected-old projections were removed, and the prose now says
the theorem adapts an already supplied boundary to source-coordinate residual
and following-factor functions.

The rereview passed with no remaining source-fidelity or formalisation
findings. It confirmed that only displayed-pivot principalization projections
remain, that the source-coordinate theorem is an adapter over supplied data,
and that the row/column domains and displayed pivot normalization are honest.

## Caveats

- This does not construct the selected-old chart.
- This does not prove chart coverage, regularity, or transition regularity
  from coordinates.
- This does not construct the raw source pullback.
- This does not prove chart-produced recurrence or exponent post-data.
- This does not project selected-old `Unit` principalization with the displayed
  Case 1(2) pivot variable.
- This does not compute Jacobians, normal crossings, or RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
