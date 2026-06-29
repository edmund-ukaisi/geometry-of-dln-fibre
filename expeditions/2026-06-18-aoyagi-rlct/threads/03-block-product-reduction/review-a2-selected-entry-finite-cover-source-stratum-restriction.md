# Review - A2 selected-entry finite-cover source-stratum restriction

Reviewer: xhigh `Archimedes the 2nd`.

Status: PASS.  No blocking findings.

## Scope

Reviewed:

- `reproduction-a2-selected-entry-finite-cover-source-stratum-restriction.md`;
- `statement-card-a2-selected-entry-finite-cover-source-stratum-restriction.md`;
- `SelectedEntryOriginalLossLocalMeasure.lean`, theorem
  `exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower`.

## Findings

The Lean theorem matches the pen-and-paper restriction argument.  It assumes
the local subset hypothesis, calls the finite selected-entry signed-box
original-loss theorem, sets `U := Ubox ∩ Ulocal`, proves

```text
U ∩ sourceStratum ⊆ Ubox ∩ signedBox,
```

and transfers finiteness by product-measure and lower-integral monotonicity.

The source-rank stratum enters only as the restricted measure set and through
the explicit subset hypothesis.  No source-rank coverage, chart equality,
prior/Jacobian transport, normal crossings, pole order, or RLCT is silently
proved or used.

The inherited finite-cover hypotheses remain explicit: per-pivot residual
readout, adapted lower bound, density bounds, `Sres ≤ Rres`, `1 < Rres`, and
the pivot critical inequality.

## Boundary

This is a monotone-restriction consumer only.  The local inclusion

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ signedBoxSet Sres
```

remains an explicit hypothesis.
