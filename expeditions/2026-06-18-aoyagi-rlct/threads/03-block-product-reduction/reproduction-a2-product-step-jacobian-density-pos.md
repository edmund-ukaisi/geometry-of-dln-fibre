# Reproduction - A2 product-step Jacobian density positivity

Date: 2026-06-26.

Status: landed. Lean names:

```text
productReductionStepRawOrderJacobianCLM_det_isUnit
productReductionStepRawOrderJacobianAbsDet_pos
eventually_productReductionStepRawOrderJacobianAbsDet_pos_nhds
```

## Question

The weighted Haar bridge carries density

```text
|det J(z)|
```

where `J(z)` is the raw-order product-step derivative family.  For later
bounded-density handoffs we at least need the elementary fact that this
density is strictly positive on the determinant chart.

## Pen-and-Paper Check

On the raw determinant chart, the formal raw-order product-step Jacobian is a
linear equivalence.  Hence its determinant is a unit and in particular is
nonzero.  The analytic derivative family used by the measure theorem is the
continuous-linear version of that same formal linear map, so its determinant
is also nonzero.

Therefore

```text
0 < |det J(z)|
```

for every point `z` in the determinant chart.

Since the determinant chart is open, if `z0` lies in the chart then all
sufficiently nearby `z` also lie in the chart.  The same pointwise positivity
therefore holds eventually in `nhds z0`.

## Guardrails

This proves strict positivity of the Jacobian density and a local eventual
positivity statement.  It does not prove continuity of the density, an upper
bound, a two-sided local unit estimate, original DLN source/prior transport,
source coverage, normal crossings, pole order, or RLCT.
