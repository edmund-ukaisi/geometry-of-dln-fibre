# Statement Card - A2 product-step Jacobian density positivity

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

Lean proves that the absolute determinant density of the raw-order p. 13
product-step derivative is strictly positive on the raw determinant chart, and
eventually positive near any determinant-chart point.

## Lean Names

```text
productReductionStepRawOrderJacobianCLM_det_isUnit
productReductionStepRawOrderJacobianAbsDet_pos
eventually_productReductionStepRawOrderJacobianAbsDet_pos_nhds
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype pi] [Fintype mu] [Fintype nu]`;
- membership in `productReductionStepRawDetChartSet rho pi mu nu`.

## Not Proved

This is not continuity of the density, not local boundedness above, not a
two-sided unit estimate, not original source/prior transport, not source
coverage, not normal crossings, and not an RLCT or pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

Verified on 2026-06-26 with the focused module build passing.
