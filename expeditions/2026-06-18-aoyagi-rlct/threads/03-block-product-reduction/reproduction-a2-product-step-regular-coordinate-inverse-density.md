# Reproduction - A2 p.13 regular-coordinate inverse density handoff

Date: 2026-06-26.

Status: landed and reviewed.  Lean names:

```text
paperEndpointFixedBaseP13RawOrderTuple
paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet
paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_selfBase
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
```

This checkpoint also uses the generic composition helpers:

```text
continuousAt_productReductionStepRawOrderInverseJacobianDensity_comp_of_mem_rawDetChartSet
productReductionStepRawOrderInverseJacobianDensity_comp_pos_of_mem_rawDetChartSet
```

## Question

The previous checkpoint proved local unit control for the chart-side inverse
Jacobian density of one p. 13 product step on an abstract raw-shaped target
tuple

```text
(Ctop, D, F3, A1, F2, A3, C).
```

The next elementary bridge is to feed this theorem the explicit p. 13
multi-edge regular-coordinate family.  The point is only to identify the
one-step left-endpoint target tuple and prove the determinant chart and
continuity hypotheses needed by the existing density theorem.

## Pen-and-Paper Check

Let

```text
j  = Fin.last (M + 2),
p0 = 0,
one = p0.succ.
```

For a base reversed-edge family `Ebase(x)`, write

```text
Dtail(x) = residualProduct(Ebase(x), j, one),
C0(x)    = residualBlock(Ebase(x), j, p0).
```

For the Euclidean regular coordinate vector `u`, decode the three regular
blocks as

```text
Ctop(u) = I + X(u),
F2(u),
F3(u).
```

The p. 13 left-endpoint product-coordinate matrix is

```text
[ Ctop(u)   -Ctop(u) F2(u) ]
[ 0          C0(x)          ].
```

Immediately before this left step, the already-treated tail suffix has
top-left accumulator `I`, tail residual product `Dtail(x)`, and lower-left
regular field `F3(u)`.  Therefore the one-step raw input is

```text
C1     = I,
D      = Dtail(x),
F3_old = F3(u),
A1     = Ctop(u),
A2     = -Ctop(u) F2(u),
A3     = 0,
A4     = C0(x).
```

Applying the p. 13 one-step chart formulas gives

```text
Ctop = C1 A1 = Ctop(u),
D    = Dtail(x),
A1   = Ctop(u),
A3   = 0,
F2   = -A1^{-1} A2 = F2(u),
F3   = F3_old - D A3 (C1 A1)^{-1} = F3(u),
C    = A4 - A3 A1^{-1} A2 = C0(x).
```

Thus the raw-shaped target tuple that should be fed to
`productReductionStepChartCoordinatesOfRawOrderTopologyTuple` is

```text
Y(x,u) =
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

The key point is that the passive `A1` slot is `Ctop(u)`, not the identity
matrix.  The identity is the pre-left-step accumulator `C1`.

## Determinant Chart

The raw-shaped target determinant set checks only the first and fourth slots:

```text
IsUnit det(Ctop) and IsUnit det(A1).
```

For `Y(x,u)`, both slots are the same matrix `Ctop(u)`.  At the centered
regular coordinate `u = 0`, `Ctop(0) = I`, so `det Ctop(0) = 1`, a unit in
`R`.  This proves determinant-chart membership at every base parameter
`(x,0)`.

## Continuity

The tuple varies continuously at a self-base point `(x0,0)` when the base edge
family is continuous at `x0` and equals the fixed paper chain there.

The regular blocks `Ctop(u)`, `F2(u)`, and `F3(u)` are continuous functions of
the Euclidean coordinate vector.  The residual product `Dtail(x)` and residual
block `C0(x)` are continuous by the suffix-state topology API, using the
self-base recursive determinant-chart hypotheses from the fixed-base chart
theorem.  The zero `A3` block is constant.

Composing this continuous tuple with the abstract chart-side inverse-density
theorem gives continuity of

```text
productReductionStepRawOrderInverseJacobianDensity(Y(x,u))
```

at `(x0,0)`.  The same determinant-chart membership gives strict positivity at
that point.

## Guardrails

This is a local tuple and local reciprocal-density handoff for the p. 13
regular-coordinate chart.  It does not prove original DLN source/prior
transport, source coverage, an unweighted measure pushforward theorem, normal
crossings, pole order, or RLCT.
