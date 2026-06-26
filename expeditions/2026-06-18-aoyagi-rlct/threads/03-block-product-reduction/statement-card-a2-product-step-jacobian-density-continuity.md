# Statement Card - A2 product-step Jacobian density continuity

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

Lean proves that the source-side forward raw-order product-step Jacobian
density is continuous at every raw determinant-chart point, and therefore has
positive lower and upper bounds on a sufficiently small neighborhood.

## Lean Names

```text
continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderJacobianAbsDet_nhds
exists_pos_eventually_productReductionStepRawOrderJacobianAbsDet_le_nhds
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype pi] [Fintype mu] [Fintype nu]`;
- membership in `productReductionStepRawDetChartSet rho pi mu nu`.

## Method

The proof first proves continuity after applying the continuous-linear
Jacobian family to a fixed tangent vector, by expanding Aoyagi's formal p. 13
derivative formula.  A finite basis then reconstructs continuity of the whole
continuous-linear-map valued family.  The density theorem composes with
`ContinuousLinearMap.continuous_det` and absolute value.

## Not Proved

This is not original DLN source/prior transport, not a chart-side inverse
density theorem, not source coverage, not normal crossings, and not an RLCT or
pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

Verified on 2026-06-26 with the focused module build, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check` passing.  The full build
reported only pre-existing warnings in unrelated files.
