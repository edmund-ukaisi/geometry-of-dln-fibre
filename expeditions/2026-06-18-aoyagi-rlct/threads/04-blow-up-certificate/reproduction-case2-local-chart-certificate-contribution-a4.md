# Reproduction - Case 2 local chart-certificate contribution

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-local-chart-certificate-contribution-a4.md`.

## Source Anchor

Aoyagi PDF p. 6 reads the finite normal-crossing contribution from a chart
coordinate with loss exponent `k_j` and Jacobian/prior exponent `h_j` through

```text
(h_j + 1) / (2 k_j).
```

For the displayed continuing Case 2 chart on PDF pp. 19-22, earlier A4 slices
already isolated the residual-block selected-entry calculation.  The residual
center is represented in Lean by

```text
E = case2ResidualBlockPivotEntries n S J,
```

and the displayed pivot is

```text
p = (J+1,J+1).
```

Under the displayed continuation hypothesis, `p in E`.  The local one-chart
microcertificate

```text
case2DisplayedCenterSqFormalJacobianChartCertificate n hS hcont
```

packages only the selected-entry center square-sum and the formal pivot-first
determinant for this displayed chart.  The source-side finite certificate

```text
Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
```

records the matching center-square identity, formal determinant exponent, and
the cardinality identity `card(E.erase p) + 1 = card(E)`.

This slice only bundles those already-proved local facts into a single local
contribution statement.

## Pen-and-Paper Calculation

The local selected-entry chart has one distinguished coordinate `u` and
residual coordinates for `E \ {p}`:

```text
x_p = u,
x_e = u y_e    for e in E \ {p}.
```

The local finite loss is the center square-sum:

```text
sum_(e in E) x_e^2
  = u^2 * (1 + sum_(e in E \ {p}) y_e^2).
```

Thus the loss exponent of the single normal-crossing coordinate is

```text
k = 1.
```

The formal pivot-first coordinate matrix is block lower triangular:

```text
[ 1   0  ]
[ y   uI ].
```

Its determinant is

```text
u ^ card(E \ {p}),
```

so the formal Jacobian/prior exponent of the same coordinate is

```text
h = card(E \ {p}).
```

Since `p in E`,

```text
card(E \ {p}) + 1 = card(E).
```

Therefore the local finite ratio is

```text
(h + 1) / (2 k)
  = (card(E \ {p}) + 1) / 2
  = card(E) / 2.
```

The microcertificate has one chart and one coordinate.  The coordinate is
active because `k = 1 > 0`.  Consequently:

```text
local ratio at the unique coordinate = card(E) / 2,
local finite exponent minimum        = card(E) / 2,
local chart count at that ratio      = 1,
local minimum-coordinate count       = 1,
local finite exponent order          = 1.
```

The source certificate supplies the same formal determinant/cardinality data,
so the existing local exponent-coordinate bridge also holds for this
microcertificate's own exponent data.  The bundle does not use the local count
as a global pole-order count.

## Lean Target

Add a local summary theorem in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`, inside
`case2DisplayedCenterSqFormalJacobianChartCertificate`:

```text
localChartCertificateContribution_summary
```

The theorem should return the existing local bridge plus the local ratio,
minimum, ratio-count, minimum-count, and order facts for

```text
Cnc = case2DisplayedCenterSqFormalJacobianChartCertificate n hS hcont.
```

## Boundary

This is a local finite contribution only.

It proves no global A0 chart family, no selected-entry atlas, no chart
coverage, no source production of successor charts or suffixes, no analytic
Jacobian or volume-form theorem, no transition regularity, no global
active-ratio lower bound, no global chart-count theorem, no pole order, and no
RLCT extraction.

## Kill Conditions

- Do not identify this local one-chart microcertificate with the full DLN loss
  normal-crossing certificate.
- Do not use its local `exponentMinimum` as the global A0 exponent minimum.
- Do not use its local chart count or exponent order as Aoyagi's global pole
  order.
- Do not treat the formal pivot-first determinant as an analytic volume-form
  theorem.
