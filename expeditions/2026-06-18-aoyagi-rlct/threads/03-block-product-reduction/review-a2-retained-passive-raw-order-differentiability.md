# Review - A2 Retained-Passive Raw-Order Differentiability

Date: 2026-06-26.

Reviewer: Carver the 4th, xhigh read-only explorer.

## Verdict

No findings.

## Checks

Carver checked the new theorem
`differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet`
against the raw-order component lemmas in
`RetainedPassiveCoordinatesTopology.lean`.

The review confirmed:

```text
topologyTupleEdgeRawOrder_A1passive
topologyTupleEdgeRawOrder_F2
topologyTupleEdgeRawOrder_A3passive
topologyTupleEdgeRawOrder_C
topologyTupleEdgeRawOrder_Ctop
topologyTupleEdgeRawOrder_F3
```

match the Lean proof, including the sensitive indices:

```text
p.succ.succ
p.castSucc
(0 : Fin (M + 1)).succ
Fin.last M
```

The theorem states only `DifferentiableAt` for `topologyTupleEdgeRawOrder`.
It introduces no Jacobian determinant, measure transport, normal-crossing,
pole-order, or RLCT claim.  The proof uses only local coordinate formulas and
differentiability closure lemmas, with no quiver-paper input.

## Residual Risk

The next risk is in the future formal tangent equivalence and determinant
unit/formula layer, not in this differentiability-only assembly.

