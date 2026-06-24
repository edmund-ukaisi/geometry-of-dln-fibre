# Reproduction - A4 Case 2 displayed transition microcertificate contribution

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  Aoyagi prints the displayed top-left
selected-entry chart.  The surrounding all-pivot selected-entry chart family is
our finite formal wrapper around the same elementary selected-entry algebra;
this slice transitions an arbitrary wrapper chart to Aoyagi's displayed chart
and then uses the already formalised displayed Case 2 finite
center-square/formal-Jacobian certificate.  It does not add analytic chart
construction.

## Reproduction

Let `p` be a source selected residual-block pivot chart in the finite all-pivot
wrapper, and let the displayed target pivot be

```text
q = (J+1,J+1).
```

Write the source normalized residual-block coordinate as

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r.
```

On the displayed overlap assume

```text
d := x_q != 0.
```

The transition-generated displayed coordinates are

```text
targetU = u*d,
targetResidual_r = x_r/d.
```

The selected-entry transition equality says that the displayed chart map at
the transition point has the same residual-block value as the original source
chart point:

```text
chartMap_q(sourceChartTransitionPoint p q u residual)
  = chartMap_p(sourceChartPoint p u residual).
```

Therefore the finite selected-entry loss at the displayed transition point is
the source selected center square:

```text
loss_q(transition point)
  = selectedEntryCenterSq(center, sourceSelectedChartMap_p(u,residual)).
```

The unit and formal determinant remain target-chart data.  In target variables
they are

```text
lossUnit_q(transition point)
  = selectedEntryCenterSqUnitFactor(center.erase q, targetResidual),

jacobianPrior_q(transition point)
  = det selectedEntryPivotFirstJacobian(targetU,targetResidual).
```

Consequently the finite monomial identities at the same transition point are

```text
source center square
  = lossUnit_q(transition point) *
    product_j coord_q(transition point)_j^(2*k_qj),

target formal determinant
  = jacobianPriorUnit_q(transition point) *
    product_j coord_q(transition point)_j^(h_qj).
```

Independently, the displayed continuing finite center-square/formal-Jacobian
certificate can be constructed for the transition-generated displayed data
`(targetU,targetResidual)`.  Feeding that certificate and the displayed chart
index into the existing local contribution summary gives:

```text
loss exponent = 1,
jacobian/prior exponent = #center - 1,
ratio = #center / 2,
finite local minimum = #center / 2,
chart count at that ratio = 1,
minimum-count in the displayed chart = 1,
finite local order = 1.
```

For the Case 2 residual block,

```text
#center = (prefixMinNat n S - J) * (n(S+1) - J).
```

The new Lean theorem packages these statements together.  The packaging is
useful because later chart-certificate code can consume one transition
summary rather than separately rebuilding the displayed target data, the
finite certificate, the transition loss/unit/Jacobian identities, and the
local exponent/count facts.

## Lean Target

Landed theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero
```

It returns an existential displayed continuing
`Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate`
for the transition-generated displayed data and the bundled finite facts
listed above.

## Boundary

- The denominator is the normalized target coordinate `x_(J+1,J+1)`, not
  `u*x_(J+1,J+1)`.
- The loss becomes source-facing only through chart-map equality.
- The loss unit and formal Jacobian/prior determinant remain target displayed
  chart data.
- This does not source-produce `Csucc`, suffixes, or successor charts.
- This does not prove analytic transition regularity, chart coverage, global
  A0 normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- Do not identify target unit/determinant data with source-chart unit data.
- Do not use this local displayed contribution as a global active-ratio lower
  bound or chart-count theorem.
- Do not treat the finite formal determinant as an analytic Jacobian or volume
  theorem.
