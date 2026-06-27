# Statement Card - A2 Retained-Passive Raw-Order C1 and Density Continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
contDiffAt_matrix_inv_of_isUnit_det
contDiffAt_matrix_mul
contDiffAt_matrix_submatrix
contDiffAt_matrix_fromBlocks
contDiffAt_schurResidualBlock
contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet
continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-c1-density-continuity.md
```

## Claim

At every retained-passive tuple determinant-chart point, the forward raw-order
coordinate map is `C^1`; therefore its Frechet derivative, fixed-vector
derivative application, and forward absolute determinant density are continuous
at that point.  Consequently the forward absolute determinant density has
positive local lower and upper bounds near the chart point.

## Method

The proof mirrors the existing differentiability chain:

- replace projection differentiability by `ContDiffAt` projection lemmas;
- prove finite matrix/block helpers for inverse, multiplication, submatrix,
  block assembly, and Schur residuals;
- rerun the retained-passive solved `A1`/`A3` recursions with `ContDiffAt`;
- assemble the raw-order components by finite `pi` and product `C^1` closure;
- use `ContDiffAt.continuousAt_fderiv`, determinant continuity, and absolute
  value continuity.

## Role

This removes the local determinant-density continuity hypothesis for the
retained-passive raw-order chart.  Downstream measure/COV statements can now
obtain local positive bounds for `topologyTupleEdgeRawOrderFDerivAbsDet`
directly from determinant-chart membership.

## Nonclaims

No explicit determinant formula, inverse-density measurability, source-prior
transport, original DLN source pushforward, selected-entry target-image
equality, source-rank coverage, normal crossings, pole order, or RLCT statement
is proved here.
