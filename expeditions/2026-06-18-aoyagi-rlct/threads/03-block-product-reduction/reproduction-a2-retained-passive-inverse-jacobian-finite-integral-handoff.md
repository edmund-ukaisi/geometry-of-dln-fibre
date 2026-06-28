# Reproduction - A2 retained-passive inverse-Jacobian finite-integral handoff

## Shape

The raw-order retained-passive inverse-Jacobian source measure is

```text
mu :=
  map rawChart
    ((m.restrict T).withDensity
      (fun y => ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y))).
```

Here `T` is the raw-order source-recursive determinant chart and `rawChart` is
the public fixed-base p.13 raw-order source chart.  Let

```text
directChart z :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple z),
```

with `z` ranging over the determinant chart `S`.

The desired finite-integral theorem should not ask for local-source residual
positivity and local residual negative-power integrability directly.  Instead,
it assumes the source-space measurability input

```text
MeasurableSet {x | residualSquareSum x > 0},
```

and the determinant-chart residual facts

```text
for m.restrict S-a.e. z, residualSquareSum (directChart z) > 0,
integral over m.restrict S of residualSquareSum (directChart z)^(-t) is finite.
```

The local loss lower bound and local density bounds remain the same inputs as
the retained-passive local finite-integral socket.

## Calculation

The already proved residual-source handoff gives:

```text
for mu.restrict localSource-a.e. x,
  residualSquareSum x > 0,

residualNegPowerIntegrableOn localSource mu t.
```

It obtains these from the determinant-chart residual hypotheses by combining
the direct source-chart/raw-order inverse-Jacobian measure comparison with the
raw-order source-chart support theorem.

The retained-passive p.13 local finite-integral socket then applies with

```text
alpha := EFam,
x0 := base,
Cedge := fun E => E,
mu := raw inverse-Jacobian source measure.
```

The source-data base identity is `rfl`, and `Cedge` is continuous by
`continuous_id`.  The socket returns an open neighborhood `U` of the base such
that the p.13 regular-coordinate local integral is finite over

```text
(mu.restrict (U ∩ sourceStratum)).prod nu.
```

## Boundary

This proves a retained-passive chart-layer finite-integral handoff for the
raw-order inverse-Jacobian source measure.  It does not prove the
source-space residual positive-set measurability, determinant-chart residual
hypotheses, selected-entry residual integrability, source-rank coverage,
original external DLN source-prior transport, normal crossings, pole order, or
RLCT extraction.
