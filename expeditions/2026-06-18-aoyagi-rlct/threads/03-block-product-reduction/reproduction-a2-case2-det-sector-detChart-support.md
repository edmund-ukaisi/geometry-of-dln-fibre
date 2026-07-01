# Reproduction - A2 Case 2 determinant-sector determinant-chart support

Date: 2026-07-01.

Status: pen-and-paper reproduction for determinant-chart support of localized
full passive-theta sources.

## Question

Let

```text
Y(theta) = case2PassiveThetaEndpointTopologyTuple theta
```

be the endpoint retained-passive topology-tuple map on the full
`Case2PassiveTheta` coordinate domain.  Suppose a measurable local theta set
`Omega` lies inside the passive determinant sector

```text
case2PassiveThetaDetSector
  = {theta | IsUnit theta.Ctop.det
      and forall p : Fin 1, IsUnit (theta.A1passive p).det}.
```

What support statement follows for the pushforward of any theta-domain measure
restricted to `Omega`?

## Calculation

For every `theta in Omega`, the subset hypothesis gives the determinant-sector
condition.  The already-formalized determinant-chart membership theorem says

```text
theta in case2PassiveThetaDetSector
  -> Y(theta) in topologyTupleDetChartSet.
```

Therefore

```text
forall theta in Omega, Y(theta) in topologyTupleDetChartSet.
```

Since `Omega` is measurable, this pointwise statement is an a.e. statement for
any restricted theta measure:

```text
forall^ae theta with respect to thetaMeasure.restrict Omega,
  Y(theta) in topologyTupleDetChartSet.
```

The determinant-chart target is open, hence measurable.  If `Y` is
a.e.-measurable on the restricted theta measure, `ae_map_iff` transports the
support statement to the pushforward:

```text
forall^ae y with respect to Measure.map Y (thetaMeasure.restrict Omega),
  y in topologyTupleDetChartSet.
```

Thus restricting the pushforward to the determinant-chart target changes
nothing:

```text
(Measure.map Y (thetaMeasure.restrict Omega)).restrict
    topologyTupleDetChartSet
  = Measure.map Y (thetaMeasure.restrict Omega).
```

## Boundary

This proves only determinant-chart support for sources already localized
inside the passive determinant sector.  It does not construct the passive
Haar/Lebesgue reference measure, compute a Jacobian, identify the pushforward
with determinant-chart Haar, prove domination by Haar, compare an original
source prior, prove source-rank coverage, construct normal crossings, compute
pole order, or extract an RLCT.
