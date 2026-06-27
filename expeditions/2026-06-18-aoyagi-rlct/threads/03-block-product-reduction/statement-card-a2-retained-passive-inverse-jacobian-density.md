# Statement Card: A2 retained-passive inverse Jacobian density

## Claim

For the retained-passive raw-order chart map, define the chart-side inverse
Jacobian density by pulling the forward absolute determinant back through the
source-readback inverse and taking the reciprocal.  On the determinant chart it
cancels the forward density pointwise.  With explicit a.e.-measurability
hypotheses, the unweighted pushforward of Haar restricted to the determinant
chart is Haar on the raw source-recursive chart weighted by this inverse
density.

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

New intended names:

```text
topologyTupleEdgeRawOrderInverseJacobianDensity
topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
```

## Hypotheses

The pointwise theorems use only:

- `z in topologyTupleDetChartSet`;
- the raw-order inverse laws;
- positivity of the forward derivative absolute determinant on the determinant
  chart.

The conditional measure theorem additionally assumes:

- `m` is an additive Haar measure;
- the determinant-chart set is null-measurable for `m`;
- the forward density is a.e.-measurable on `m.restrict S`;
- the inverse density is a.e.-measurable on `m.restrict T`;
- the inverse density after composition with the raw-order map is
  a.e.-measurable on `m.restrict S`.

## Nonclaims

This checkpoint does not prove:

- an explicit determinant formula;
- continuity of `topologyTupleEdgeRawOrderFDerivAbsDet`;
- measurability of the forward or inverse density without hypotheses;
- source-prior density identity;
- original DLN source pushforward;
- normal crossings, pole order, or RLCT.

## Verification Plan

1. Build `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesMeasure`.
2. Ask an independent xhigh reviewer to audit the statement against the
   reproduction and the missing-continuity boundary.
3. Run the full `DLNFibre` build and forbidden-marker scan before committing.
