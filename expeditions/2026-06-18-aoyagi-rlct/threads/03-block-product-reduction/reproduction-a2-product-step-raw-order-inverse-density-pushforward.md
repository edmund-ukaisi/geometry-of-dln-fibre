# Reproduction - A2 product-step raw-order inverse-density pushforward

Date: 2026-06-26.

Status: proved and reviewed.  Lean target:

```text
ProductReductionStepMeasure.lean
```

## Question

The landed raw product-step change-of-variables theorem proves the weighted
forward identity on the determinant chart:

```text
Phi_* ((m|s) with density J) = m|s,
```

where

```text
s = productReductionStepRawDetChartSet,
Phi = productReductionStepTopologyTupleToChartRawOrder,
J(z) = productReductionStepRawOrderJacobianAbsDet z.
```

The next measure-theoretic bridge is the same coordinate change in the
unweighted source orientation:

```text
Phi_* (m|s) = (m|s) with density (J o Phi^{-1})^{-1}.
```

In Lean the chart-side reciprocal density is already named

```text
productReductionStepRawOrderInverseJacobianDensity y
  = (J (((productReductionStepChartCoordinatesOfRawOrderTopologyTuple y).toRaw).topologyTuple))^{-1}.
```

This is a raw product-chart statement only.  It does not construct the p. 13
source chart from original DLN coordinates.

## Pen-and-Paper Check

On the determinant chart write

```text
z = (C1,D,F3old,A1,A2,A3,A4),
```

with `det C1` and `det A1` nonzero.  The raw-order product-step map is

```text
Phi(z) =
(C1*A1, D,
 F3old - D*A3*(C1*A1)^(-1),
 A1, -A1^(-1)*A2, A3, A4 - A3*A1^(-1)*A2).
```

The inverse raw-coordinate reconstruction on the target determinant chart is

```text
Psi(y) =
(Ctop*A1^(-1), D, F3 + D*A3*Ctop^(-1),
 A1, -A1*F2, A3, C - A3*F2).
```

Substituting `y = Phi(z)` gives `Psi(Phi(z)) = z`; substituting
`z = Psi(y)` gives `Phi(Psi(y)) = y`.  Thus `Phi` is a bijection `s -> s`.

Let

```text
J(z) = |det D Phi_z|,
K(y) = productReductionStepRawOrderInverseJacobianDensity y
     = J(Psi(y))^{-1}.
```

Then on `s`,

```text
K(Phi(z)) = J(z)^{-1},
J(z) * K(Phi(z)) = 1.
```

The weighted COV identity gives

```text
Phi_* ((m|s) with density J) = m|s.
```

Since `J * (K o Phi) = 1` on the `m|s`-support, the source restriction can be
rewritten as

```text
m|s = ((m|s) with density J) with density (K o Phi).
```

Pushing forward and transporting the second density through the a.e.-measurable
map `Phi` gives

```text
Phi_* (m|s)
  = Phi_* (((m|s) with density J) with density (K o Phi))
  = (Phi_* ((m|s) with density J)) with density K
  = (m|s) with density K.
```

This proof uses the existing forward derivative theorem and determinant-chart
bijectivity.  It should not require a new derivative computation for `Psi`.

## Lean Shape

Preferred direct theorem:

```text
Measure.map productReductionStepTopologyTupleToChartRawOrder
  (m.restrict productReductionStepRawDetChartSet)
=
(m.restrict productReductionStepRawDetChartSet).withDensity
  (fun y => ENNReal.ofReal
    (productReductionStepRawOrderInverseJacobianDensity y)).
```

If the direct theorem is blocked by global measurability of `Phi` or `K`, the
honest fallback is a subtype determinant-chart version using
`Set.restrict Phi : s -> s` and the measure
`Measure.comap Subtype.val (m.restrict s)`.  That theorem is still a real raw
product-chart transport result, but the direct ambient version is more useful.

## Kill Conditions

- If the proof needs a new inverse-map Jacobian theorem, this slice is larger
  than intended and should be parked or split.
- If the statement forgets the determinant-chart restriction, it is false as a
  coordinate-change claim.
- If the result is described as original DLN source/prior transport, it
  overclaims.  This is only raw product-step Haar transport.

## Guardrails

This checkpoint does not prove p. 13 source coverage, product-chart source
construction, signed-box density identification, regular-suspension
construction, normal crossings, pole order, or RLCT.
