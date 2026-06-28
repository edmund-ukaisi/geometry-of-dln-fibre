# Reproduction - A2 retained-passive inverse-Jacobian residual-source handoff

## Shape

The latest chart-layer measure comparison identifies two source measures:

```text
map directChart (m.restrict S)
  =
map rawChart ((m.restrict T).withDensity inverseJacobianDensity).
```

Here `S` is the retained-passive determinant chart, `T` is the raw-order
source-recursive determinant chart,

```text
directChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple z),
```

and `rawChart` is the public raw-order p.13 source chart.  The next handoff
uses this equality to produce the residual-source hypotheses needed by the
p.13 local-measure socket for the inverse-Jacobian raw-order source measure

```text
mu :=
  map rawChart
    ((m.restrict T).withDensity
      (fun y => ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y))).
```

The chart-side inputs are:

```text
measurability of the positive residual-square-sum set,
for a.e. z in m.restrict S, residualSquareSum (directChart z) > 0,
finite integral of residualSquareSum (directChart z)^(-t) over m.restrict S.
```

The conclusion is:

```text
ae positivity of residualSquareSum on mu.restrict localSource,
residualNegPowerIntegrableOn localSource mu t.
```

## Calculation

Let

```text
localSource :=
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0
    (fun E => E).
```

To use `residualSourceHypotheses_of_measure_map`, we need

```text
mu.restrict localSource = map directChart (m.restrict S).
```

There are two pieces.

First, the proof factors a density-independent support lemma.  For any density
`J`, the raw-order source chart maps every `y in T` into the fixed-base
retained-passive source-edge-family set, which is the identity-`Cedge` local
source:

```text
map rawChart ((m.restrict T).withDensity J)
  restricted to localSource
=
map rawChart ((m.restrict T).withDensity J).
```

The pointwise input is that the fixed-base edge matrices of `rawChart y` are
`edgeFamilyOfRawOrderTuple y`; the local-source membership lemma then applies.
Since `(m.restrict T).withDensity J` is absolutely continuous with respect to
`m.restrict T`, this pointwise membership on `T` holds a.e. for the weighted
measure.  Specializing this support lemma to

```text
(m.restrict T).withDensity inverseJacobianDensity.
```

gives

```text
mu.restrict localSource = mu.
```

Second, the already proved inverse-Jacobian chart measure theorem gives

```text
map directChart (m.restrict S) = mu.
```

Combining these gives the required map equality:

```text
mu.restrict localSource = map directChart (m.restrict S).
```

Now apply `residualSourceHypotheses_of_measure_map` with

```text
chart := directChart,
nu := m.restrict S,
source := localSource.
```

The residual positivity and finite residual negative-power integral are
exactly the chart-side assumptions.

## Boundary

This proves residual-source positivity and residual negative-power
integrability for the retained-passive inverse-Jacobian raw-order source
measure from direct determinant-chart hypotheses.

It does not prove those chart-side residual hypotheses, source-rank coverage,
selected-entry residual positivity, normal crossings, pole order, RLCT
extraction, or identification with an original external DLN prior.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The inverse-Jacobian raw-order source measure
satisfies the p.13 residual-source hypotheses whenever the direct
determinant-chart pullback has a.e. positive residual square-sum and finite
residual negative-power integral.

**Assumed.** Finite-dimensional fixed-base context, measurable/Borel
structures on topology tuples and edge families, Haar measure on topology
tuples, source-side positive-set measurability, and the two direct chart-side
residual hypotheses.

**Deferred.** Proof of the direct chart-side residual positivity and integral,
source-rank coverage, selected-entry specialization, normal crossings, pole
order, RLCT extraction, and original external prior transport.
