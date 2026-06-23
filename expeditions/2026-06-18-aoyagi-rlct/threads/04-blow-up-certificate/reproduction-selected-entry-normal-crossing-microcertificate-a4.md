# Reproduction - selected-entry finite normal-crossing microcertificate

Date: 2026-06-23.

Status: reproduced, formalised, reviewed.

## Source Anchor

Aoyagi PDF p. 5 uses a square-sum of ideal generators for the local loss
convention.  Aoyagi PDF p. 6 reads finite normal-crossing exponents from a
display of the form

```text
loss = unit * product_j coordinate_j^(2 k_j),
jacobian/prior = unit' * product_j coordinate_j^(h_j).
```

In Case 2 on PDF pp. 19-21, the displayed selected-entry blow-up chart for
the residual-block center is

```text
d_(J+1,J+1) = u_(S,J+1),
d_(i,j) = u_(S,J+1) d'_(i,j)       for all other residual-block entries.
```

Earlier A4 slices proved the finite square-sum pullback and the formal
pivot-first determinant calculation.  This slice packages exactly those two
finite calculations as a one-chart `AoyagiNormalCrossingChartCertificate`.
It does not claim that this one chart is the global Aoyagi resolution, and it
does not upgrade the formal determinant to an analytic volume-form theorem.

## Pen-and-Paper Calculation

Let `E` be a finite center, and let `p in E` be the selected pivot.  The
selected-entry chart has one distinguished coordinate `u` and residual
coordinates `y_e` for `e != p`:

```text
x_p = u,
x_e = u y_e    for e in E \ {p}.
```

The finite center square-sum pulls back as

```text
sum_(e in E) x_e^2
  = u^2 + sum_(e != p) (u y_e)^2
  = u^2 * (1 + sum_(e in E \ {p}) y_e^2).
```

Over an ordered field, the factor

```text
1 + sum_(e in E \ {p}) y_e^2
```

is positive, hence nonzero, hence a field unit.  Therefore, for the one
normal-crossing coordinate `u`, the loss exponent in Aoyagi's convention is

```text
k = 1.
```

For the formal pivot-first coordinate matrix, order the variables as
`(u, y_e)_{e in E \ {p}}` and the old center coordinates as
`(x_p, x_e)_{e in E \ {p}}`.  The finite matrix is

```text
[ 1   0  ]
[ y   uI ].
```

Its determinant is

```text
u ^ |E \ {p}|.
```

Thus the formal Jacobian/prior exponent of the coordinate `u` is

```text
h = |E \ {p}|.
```

The Lean certificate keeps this indexing discipline: the parameter is a value
function on the finite center subtype, while the chart residuals are indexed
only by the erased center `E \ {p}`.  An ambient residual function is used
internally only to reuse the existing selected-entry square-sum lemma.

For Aoyagi's displayed Case 2 residual center

```text
E = case2ResidualBlockPivotEntries n S J,
p = (J+1,J+1),
```

the existing continuation hypothesis proves `p in E`, so the same
microcertificate has

```text
k = 1,
h = card(E.erase p).
```

The existing Case 2 finite bridge then applies to this microcertificate's own
one-coordinate exponent data.  This is not a substitute for the full A0
global exponent data: it records only the local residual-center square-sum
and formal selected-entry determinant.

## Lean Names

```text
selectedEntryCenterSqFormalJacobianChartCertificate
selectedEntryCenterSqFormalJacobianChartCertificate.lossExp_zero_zero
selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero
case2DisplayedCenterSqFormalJacobianChartCertificate
case2DisplayedCenterSqFormalJacobianChartCertificate.lossExp_zero_zero
case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero
Case2DisplayedContinuingExponentCoordinateBridge
case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge
```

## Proved

- A generic selected-entry one-chart finite certificate whose parameter is a
  finite center value function.
- Its chart residual coordinates are indexed by the non-pivot finite center
  entries.
- Its loss is the finite center square-sum.
- Its loss unit is the normalized square-sum factor, with an `IsUnit` witness
  over an ordered field.
- Its Jacobian/prior factor is exactly the formal determinant
  `u ^ card(center.erase pivot)`, with unit factor `1`.
- The unique normal-crossing coordinate has finite exponents `k = 1` and
  `h = card(center.erase pivot)`.
- The Case 2 displayed pivot specializes this certificate to
  `case2ResidualBlockPivotEntries n S J`.
- For this one-coordinate microcertificate's own exponent data, the generic
  `Case2DisplayedContinuingExponentCoordinateBridge` is no longer a supplied
  field: the bridge is constructed by reflexive exponent-array equalities.
  The A0-facing wrapper
  `Case2DisplayedContinuingA0ExponentCoordinateBridge` remains reserved for
  later finite exponent data meant to represent the full A0
  normal-crossing problem.

## Not Proved

- No chart coverage.
- No source production of a successor chart or suffix.
- No analytic regularity or transition regularity.
- No analytic nonvanishing neighbourhood theorem beyond the algebraic
  `IsUnit` field in the certificate.
- No analytic Jacobian, derivative, or volume-form theorem.
- No total DLN loss monomial identity.
- No global A0 normal-crossing chart family.
- No active-ratio lower bound, pole-order count, pole order, or RLCT
  extraction.

## Kill Conditions

- Do not use this certificate as the full normal-crossing resolution of the
  DLN loss.
- Do not treat its `jacobianPrior` field as an analytic Jacobian theorem; it
  is the formal pivot-first determinant already proved in A4.
- Do not infer chart coverage or transition regularity from this one-chart
  finite package.
- Do not replace the full A0 exponent data in Theorem 2 by this
  microcertificate unless the claim is explicitly only about the local
  residual-center square-sum.
