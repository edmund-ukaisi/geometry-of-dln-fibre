# Reproduction - Case 1 local chart-certificate contributions

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case1-local-chart-certificate-contribution-a4.md`.

## Source Anchor

Aoyagi PDF p. 6 reads the finite normal-crossing ratio for a coordinate with
loss exponent `k_j` and Jacobian/prior exponent `h_j` as

```text
(h_j + 1) / (2 k_j).
```

The pole order/count in the source is global: it counts coordinates attaining
the global minimum in each chart and then takes a maximum over charts.  This
slice is not that global count.  It records only the local finite contribution
of two already-constructed one-chart Case 1 selected-entry microcertificates.

For Case 1, Aoyagi PDF pp. 15-16 uses a center consisting of the selected old
variable and a row strip.  In Lean this finite center is

```text
case1CenterGenerators n S J J1,
```

with the selected old variable represented by the `Sum.inl ()` token.  The
hidden source label behind that token remains supplied elsewhere by
`Case1SelectedOldUnitSuppliedChartFamilyBoundary`; it is not constructed by
this local microcertificate.

Aoyagi PDF pp. 16-17 also describes the displayed row-strip pivot
`(J+1,J+1)`.  Lean represents that local finite pivot by

```text
Sum.inr (J+1,J+1) : Case1CenterGenerator.
```

Both local selected-entry microcertificates use the same finite center and
have the same number of non-pivot generators:

```text
J1 * (n(S+1)-J).
```

## Pen-and-Paper Calculation

Let

```text
E = case1CenterGenerators n S J J1.
```

For either selected local pivot `p in E`, the selected-entry chart has one
distinguished coordinate `u` and residual coordinates for `E \ {p}`:

```text
x_p = u,
x_e = u y_e    for e in E \ {p}.
```

The local finite center square-sum pulls back as

```text
sum_(e in E) x_e^2
  = u^2 * (1 + sum_(e in E \ {p}) y_e^2),
```

so the loss exponent is

```text
k = 1.
```

The formal pivot-first coordinate matrix is

```text
[ 1   0  ]
[ y   uI ],
```

so the formal Jacobian/prior exponent is

```text
h = card(E \ {p}).
```

For both Case 1 pivots considered here, the existing finite cardinality
calculation gives

```text
card(E \ {p}) = J1 * (n(S+1)-J).
```

Therefore the local finite ratio is

```text
(h + 1) / (2 k)
  = (1 + J1 * (n(S+1)-J)) / 2.
```

Each local microcertificate has one chart and one coordinate, and that
coordinate is active because `k = 1`.  Thus for each local microcertificate:

```text
local finite minimum          = (1 + J1 * (n(S+1)-J)) / 2,
local chart count at ratio    = 1,
local minimum-coordinate count = 1,
local finite exponent order   = 1.
```

These are statements about the microcertificate's own exponent data only.
They do not compute Aoyagi's global pole order.

## Lean Target

Add two local summary theorems in
`lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`, where the generic
Case 1 bridge type already lives:

```text
case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary
```

Each theorem should bundle:

- the existing generic `Case1SelectedEntryExponentCoordinateBridge` for the
  local microcertificate's own exponent data;
- the local ratio;
- the local finite minimum;
- the local `countInChartAtRatio = 1`;
- the local `minCountInChart = 1`;
- the local finite order `1`.

Use the generic bridge, not `Case1SelectedEntryA0ExponentCoordinateBridge` or
`Case1SelectedOldUnitA0ExponentCoordinateBridge`.

## Boundary

This is local finite bookkeeping only.

It proves no global A0 chart family, no chart coverage, no selected-entry
atlas, no construction of the hidden selected-old source label, no
source-produced recurrence or exponent post-data, no Case 1 transition
theorem, no analytic Jacobian or volume-form theorem, no analytic unit
neighbourhood, no global active-ratio lower bound, no global
chart-count/order theorem, no Theorem 2 pole order, no `theta`, and no RLCT
extraction.

## Kill Conditions

- Do not use the selected-old `Unit` token as a source-produced old label
  without the separate selected-old boundary.
- Do not use either local order `1` as the global pole order.
- Do not use either local finite minimum as the global A0 exponent minimum.
- Do not treat the formal pivot-first determinant exponent as an analytic
  Jacobian or volume-form theorem.
