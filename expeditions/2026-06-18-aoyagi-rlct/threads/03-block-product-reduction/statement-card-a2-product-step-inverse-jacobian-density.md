# Statement Card - A2 product-step inverse Jacobian density

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

Lean proves that the chart-side reciprocal density
`J(toRaw(y))^{-1}` is positive and continuous at every raw-shaped target
determinant-chart point, and therefore admits positive lower and upper
eventual bounds near that point.

## Lean Names

```text
continuousAt_productReductionStepChartRawOrderToRawTopologyTuple_of_mem_rawDetChartSet
productReductionStepRawOrderInverseJacobianDensity
productReductionStepRawOrderInverseJacobianDensity_pos
continuousAt_productReductionStepRawOrderInverseJacobianDensity_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderInverseJacobianDensity_nhds
exists_pos_eventually_productReductionStepRawOrderInverseJacobianDensity_le_nhds
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype pi] [Fintype mu] [DecidableEq mu] [Fintype nu]`;
- membership in `productReductionStepRawDetChartSet rho pi mu nu`, now read as
  the raw-shaped target determinant chart.

## Method

The proof first shows that the inverse coordinate map from raw-shaped target
tuples to raw source tuples is continuous at target determinant-chart points.
The inverse map uses only `A1^{-1}` and `Ctop^{-1}`.  The raw preimage remains
in the source determinant chart, so the source-side forward density continuity
and positivity theorems apply after composition.  Inverting the positive
continuous factor gives the chart-side inverse density theorem, and the local
bounds use the same neighborhood arguments as the source-side checkpoint.

## Not Proved

This is not an unweighted source-measure pushforward theorem, not original DLN
source/prior transport, not source coverage, not normal crossings, and not an
RLCT or pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

Verified on 2026-06-26 with the focused module build.  Full-library build,
`scripts/sorries`, and `git diff --check` also passed.  The full build
reported only pre-existing warnings in unrelated files.
