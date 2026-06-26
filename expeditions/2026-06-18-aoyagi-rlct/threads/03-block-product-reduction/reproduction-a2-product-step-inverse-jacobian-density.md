# Reproduction - A2 product-step inverse Jacobian density

Date: 2026-06-26.

Status: landed. Lean names:

```text
continuousAt_productReductionStepChartRawOrderToRawTopologyTuple_of_mem_rawDetChartSet
productReductionStepRawOrderInverseJacobianDensity
productReductionStepRawOrderInverseJacobianDensity_pos
continuousAt_productReductionStepRawOrderInverseJacobianDensity_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderInverseJacobianDensity_nhds
exists_pos_eventually_productReductionStepRawOrderInverseJacobianDensity_le_nhds
```

## Question

The source-side weighted Haar theorem uses the forward density

```text
J(x) = |det D Phi(x)|
```

on the raw determinant chart.  When the same local factor is viewed in target
chart coordinates `y = Phi(x)`, the chart-side density for the original raw
Lebesgue factor is

```text
J(Phi^{-1}(y))^{-1}.
```

The previous checkpoint proved that `J` is continuous, positive, and locally
bounded above and below at source determinant-chart points.  This checkpoint
packages the corresponding local unit statement in raw-shaped target
coordinates.

## Pen-and-Paper Check

Write a raw-shaped target tuple as

```text
y = (Ctop, D, F3, A1, F2, A3, C)
```

on the determinant chart `det Ctop != 0` and `det A1 != 0`.  The inverse
coordinate map to raw source variables is

```text
C1     = Ctop A1^{-1}
D      = D
F3_old = F3 + D A3 Ctop^{-1}
A1     = A1
A2     = - A1 F2
A3     = A3
A4     = C - A3 F2.
```

Only `A1` and `Ctop` are inverted; the passive residual block `D` is not
inverted.  Hence the inverse raw-source map is continuous at every target
determinant-chart point.

The inverse raw-source point is again in the raw source determinant chart:
`A1` is unchanged and

```text
det(C1) = det(Ctop) det(A1^{-1}),
```

which is nonzero when `det Ctop` and `det A1` are nonzero.  Therefore the
already-proved source-side continuity and positivity of `J` apply at
`Phi^{-1}(y0)`.  Composition gives continuity of `J(Phi^{-1}(y))`; since it is
positive at `y0`, inversion is continuous there and
`J(Phi^{-1}(y))^{-1}` is positive.

Continuity and positivity give local bounds:

```text
J(Phi^{-1}(y0))^{-1} / 2 <= J(Phi^{-1}(y))^{-1}
```

near `y0`, and also

```text
J(Phi^{-1}(y))^{-1} <= max (J(Phi^{-1}(y0))^{-1} + 1) 1
```

after shrinking to a sufficiently small neighborhood.

## Orientation

This is the chart-side reciprocal of the forward source density.  It should
not be identified with the source-side factor `J(x)`.  The change-of-variables
identity already proved in Lean is still the forward weighted identity

```text
map Phi ((m.restrict S).withDensity J) = m.restrict S
```

after the determinant-chart image rewrite.  The present checkpoint only gives
local unit control for the reciprocal factor that appears when a source
integral is rewritten in chart variables.

## Guardrails

This proves local continuity, positivity, and positive lower/upper eventual
bounds for the chart-side inverse Jacobian density on the p. 13 determinant
target chart.  It does not prove an unweighted measure pushforward theorem,
original DLN source/prior transport, source coverage, normal crossings, pole
order, or RLCT.
