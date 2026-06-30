# Reproduction - A2 Case 2 passive theta source-measure adapter

Date: 2026-06-30.

Status: pen-and-paper check completed and formalized as the theta-specific
Lean measure-support adapter.

## Question

After introducing the full passive-sector coordinate vector

```text
theta = (A1passive, F2, A3passive, Ctop, F3, yNext),
```

what is the next honest measure-facing statement that does not yet claim
determinant-chart Haar transport?

The existing generic theorem

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

works over an arbitrary passive parameter type `eta`, with source domain

```text
eta × (center -> R).
```

The new concrete theta domain is exactly this product with

```text
eta = Case2PassiveTheta.PassiveFields.
```

Thus the immediate specialization should give a theorem for source-domain
measures on `Case2PassiveTheta`, not a theorem about the full determinant-chart
Lebesgue/Haar restriction.

## Pen-And-Paper Check

Let

```text
PassiveFields = (A1passive, F2, A3passive, Ctop, F3),
center = case2ResidualBlockPivotEntries n S (J+1).
```

Then

```text
Case2PassiveTheta = PassiveFields × (center -> R).
```

The coordinate projections used by the generic theorem are:

```text
A1passive(theta.1) = theta.A1passive,
F2(theta.1)        = theta.F2,
A3passive(theta.1) = theta.A3passive,
Ctop(theta.1)      = theta.Ctop,
F3(theta.1)        = theta.F3,
theta.2            = theta.yNext.
```

The determinant-sector hypotheses are the same:

```text
IsUnit theta.Ctop.det
forall p : Fin 1, IsUnit (theta.A1passive p).det.
```

The punctured-sector hypothesis is the selected pivot nonzero condition:

```text
theta.yNext pivotNext != 0.
```

The generic theorem produces an open set `V` around `theta0` and, for an
arbitrary source-domain measure `sourceMeasure` restricted to `V`, a
chart-produced source measure

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

with:

```text
mu.restrict localSource = mu,
Measure.map inverseReadout mu = Measure.map Prod.snd (sourceMeasure.restrict V).
```

Since `Prod.snd theta = theta.yNext` definitionally on the product theta
domain, the second identity becomes:

```text
Measure.map inverseReadout mu =
  Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V).
```

This is a chart-produced support and selected-residual marginal theorem.  It
does not identify `sourceMeasure` with the determinant-chart measure, and it
does not compare the chart-produced source measure to the original DLN source
prior.

The specialization still needs measurable/open-measurable structure on the
passive-fields product domain, because the generic theorem is measure-facing
over an arbitrary passive parameter type.  This adapter should consume those
instances rather than claim to build determinant-chart measure structure.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate chart, and pp.
19-22 support the Case 2 selected-entry residual readout.  The present step is
Lean API specialization of already-formalized finite coordinate/source-readback
facts.  It uses no quiver-paper evidence and no additional cited theorem.

## Nonclaims

This slice does not prove determinant-chart Haar transport, raw-order Haar
transport, source-prior transport, exact passive-sector pushforward, dominated
passive-sector comparison, finite-integral transfer, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
