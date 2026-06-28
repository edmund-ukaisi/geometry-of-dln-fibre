# Statement card: A2 retained-passive canonical product-density finite-integral handoff

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## Lean name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
```

## Content

The theorem specializes the retained-passive p.13 local finite-integral socket
to the canonical raw-coordinate source measure

```text
Measure.map sourceChart (m.restrict topologyTupleRawOrderSourceRecursiveDetChartSet)
```

where `sourceChart` is the retained-passive source edge-family chart built from
`ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)`.

It uses

```text
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
```

to derive the local-source residual positivity and residual negative-power
integrability required by the finite-integral socket from chart-side hypotheses
under the weighted determinant-chart measure

```text
(m.restrict topologyTupleDetChartSet).withDensity
  (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z)).
```

The remaining local loss lower bound, density nonnegativity, density upper
bound, chart-side residual positive-set measurability, chart-side residual
positivity, and chart-side finite residual integral remain hypotheses.

## Nonclaims

No original-source prior, selected-entry signed-box density identification,
monomial residual lower bound, normal-crossing production, pole-order theorem,
or RLCT theorem is claimed.
