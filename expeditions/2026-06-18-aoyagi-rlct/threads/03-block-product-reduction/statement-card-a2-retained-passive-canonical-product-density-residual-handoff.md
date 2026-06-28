# Statement card: A2 retained-passive canonical product-density residual handoff

## Lean target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobianMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Planned names

Product-density local-unit API:

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
retainedPassiveFormalRawOrderJacobianProductAbsDetAt_pos_of_mem_topologyTupleDetChartSet
continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
exists_pos_eventually_le_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_nhds
exists_pos_eventually_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_le_nhds
exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
```

Canonical residual-source handoff:

```text
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
```

## Content

The first cluster packages the named solved-`A1` product density as the actual
forward raw-order Jacobian density on the retained-passive determinant chart,
then transfers positivity, continuity, and local two-sided positive bounds from
the actual Jacobian density.

The second theorem applies the generic residual source-measure handoff using
the canonical product-density COV as its map identity.  A private helper also
proves the a.e.-measurability of the composed canonical chart under the
weighted determinant-chart measure.  The theorem keeps the chart-side residual
positivity, residual positive-set measurability, and chart-side finite integral
explicit.

## Nonclaims

No original-source prior, signed-box source-density identification, monomial
residual lower bound, normal-crossing theorem, pole-order theorem, or RLCT
theorem is claimed.
