# Reproduction - A2 product-step Jacobian density continuity

Date: 2026-06-26.

Status: landed. Lean names:

```text
continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet
continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
exists_pos_eventually_le_productReductionStepRawOrderJacobianAbsDet_nhds
exists_pos_eventually_productReductionStepRawOrderJacobianAbsDet_le_nhds
```

## Question

The weighted Haar theorem uses the source-side forward density

```text
J(x) = |det D Phi(x)|
```

for the raw-to-chart p. 13 product-step map.  The previous checkpoint proved
that `J(x)` is positive on the determinant chart.  For later local
integrability handoffs, we also need that near a determinant-chart point this
density is a bounded positive unit.

## Pen-and-Paper Check

Write the raw p. 13 variables as

```text
x = (C1, D, F3_old, A1, A2, A3, A4)
```

and restrict to the determinant chart `det C1 != 0` and `det A1 != 0`.  The
coordinate formulas use only projections, addition, matrix multiplication,
`A1^{-1}`, and `(C1 A1)^{-1}`.  At a determinant-chart point both inverse maps
are continuous, because `A1` and `C1 A1` have nonzero determinant.

The formal derivative entries are built from the same operations and inverse
terms.  Hence the continuous-linear derivative family is continuous at any
determinant-chart point.  Taking determinant and absolute value preserves
continuity, so `J` is continuous at such a point.

Since the previous checkpoint proved `J(x0) > 0`, continuity gives a smaller
neighborhood where

```text
J(x0) / 2 <= J(x) <= max (J(x0) + 1) 1.
```

Thus the forward Jacobian density is a local positive bounded unit.

## Orientation

This is a source-side statement for the forward density `|det D Phi(x)|`.
When rewriting a raw/source integral in chart variables `y = Phi(x)`, the
chart-side density is instead

```text
|det D Phi(Phi^{-1}(y))|^{-1}
```

possibly multiplied by a prior density.  The forward and inverse densities are
both harmless local units, but they are not the same measure statement.

## Guardrails

This proves local continuity and two-sided local boundedness for the
source-side forward Jacobian density on the determinant chart.  It does not
prove original DLN source/prior transport, chart-side inverse-density
transport, source coverage, normal crossings, pole order, or RLCT.
