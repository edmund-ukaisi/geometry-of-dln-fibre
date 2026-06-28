# Review - A2 retained-passive selected-entry determinant-chart residual handoff

Reviewer: Parfit, xhigh read-only review.

Status: PASS.

## Scope

Reviewed the new theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_map
```

and the accompanying reproduction and statement-card files.

## Checks

- Measure orientation is correct: the theorem assumes
  `m.restrict S = Measure.map chart weightedBox` and uses that orientation
  consistently.
- The `withDensity` absolute-continuity step is in the right direction: it
  lifts `AEMeasurable chart signedBox` to `AEMeasurable chart weightedBox`.
- The target positive-set measurability hypothesis is required and present for
  `ae_map_iff`.
- The lower-integral transport uses `lintegral_map_le` in the right direction:
  the target map integral is bounded by the source pullback integral.
- The exponent hypotheses match the selected-entry source theorem:
  `0 <= t` and
  `2 * t < ((center.erase pivot.1).card : R) + 1`.
- The documentation boundary is narrow: no chart construction, chart coverage,
  original prior transport, normal crossings, pole order, or RLCT extraction is
  claimed.

## Verification Note

The reviewer did not run Lean commands.  The controller separately ran the
focused build and gates recorded in the statement card.
