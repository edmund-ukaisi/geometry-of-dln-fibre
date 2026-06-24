# Review - A4 Case 2 chart-index residual-subtype Schur transition

Date: 2026-06-24.

Status: pass.  No blocking findings.

## Scope

Reviewed the chart-indexed residual-subtype Schur wrapper:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-chart-index-residual-subtype-schur-transition-a4.md`;
- `statement-card-a4-case2-chart-index-residual-subtype-schur-transition.md`.

## Findings

No blocking findings.

The source-boundary scout recommended Schur-compatible `Q/P` overlap data as
the next A4 step, rather than inverse/cocycle laws, because it is closer to
Aoyagi pp. 20-21 and the remaining Case 2 residual-block calculation.  The
Lean API scout confirmed the wrapper builds and identified inverse/cocycle
normalised-coordinate laws as a later finite-atlas target.

The implemented theorem is a chart-index wrapper around

```text
case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq
```

and keeps the denominator hypothesis as the normalized target coordinate
`x_ab != 0`.  It indexes the target lower-right `Q/P` block by residual-row
and residual-column subtype complements and reads their ambient source labels
as `i.1.1` and `j.1.1`.

## Gates

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full-library build completed with pre-existing Core/style warnings outside
this slice.

## Boundary Check

The slice proves only finite selected-entry and `Q/P` residual-block coordinate
algebra.  It does not prove analytic transition regularity, chart coverage,
open-neighbourhood gluing, source-displayed all-pivot atlas, successor
residual/following-factor production, analytic Jacobian/volume control, normal
crossings, pole order, or RLCT extraction.
