# Review - A2 Case 2 source-chart CenterCoord alignment

Date: 2026-06-26.

Reviewers: controller, with xhigh Lean/API scout `Nash`.

## Verdict

Pass for definitional vocabulary alignment.  The theorem states that the
displayed Case 2 source-chart map is the selected-entry center-coordinate
chart map for the same old center and displayed pivot.

## Source Check

Aoyagi pp. 19-20 support the old Case 2 selected-entry chart at pivot
`(J+1,J+1)`.  The theorem is only about that old center.  It is not a theorem
about the continuing post-pivot product `D_(J+1) * C'_+`.

## Lean/API Check

The theorem lives in `SelectedEntrySignedBoxMeasure.lean`, next to
`SelectedEntrySignedBox.CenterCoord.chartMap`, because that module already
imports the selected-entry and Case 2 source-chart names.  No finite
factor-product module imports selected-entry measure material.

The proof is `rfl`: both sides reduce to `selectedEntryChartMap` with the
displayed pivot, selected value `y pivot`, and residual function
`SelectedEntrySignedBox.CenterCoord.sourceResidual y`.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
```

## Nonclaims

No post-pivot product readout, successor source-chart readout, endpoint
equivalence, source image, chart coverage, weighted pushforward, analytic
Jacobian, normal crossings, pole order, or RLCT.
