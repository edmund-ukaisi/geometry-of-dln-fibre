# Review - A2 residual positive-set measurability handoff

Date: 2026-06-25.

Reviewer: xhigh subagent Planck the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-residual-positive-set-measurability-handoff.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-residual-positive-set-measurability-handoff.md
```

## Findings

No high or medium correctness findings.

Low documentation finding: the expedition ledgers should mention this slice
when it lands, because it removes only the explicit `hpos_meas` premise under
a global residual-coordinate measurability assumption.

## Checks

The reviewer confirmed:

- `measurable_aoyagiCoordinateSquareSum` proves finite real square-sum
  measurability by projecting measurable coordinates, multiplying them, and
  taking a finite measurable sum.
- `measurableSet_residualSquareSum_pos_of_measurable` has the intended narrowed
  scope: it assumes only measurability of the residual coordinate map and proves
  the positive-set measurability.
- The weighted signed-box corollary replaces the explicit `hpos_meas` input
  with `hres_meas`; all chart, pushforward, density, residual lower-bound, and
  residual positivity/integrability-producing hypotheses still pass through the
  existing theorem.
- The docs correctly state that residual positivity, integrability, chart
  construction, pushforward, density/Jacobian transport, normal crossings, pole
  order, and RLCT are not proved.

## Verdict

Approved after ledger update.
