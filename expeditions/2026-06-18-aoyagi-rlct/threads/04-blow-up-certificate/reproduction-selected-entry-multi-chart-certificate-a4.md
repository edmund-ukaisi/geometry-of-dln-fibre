# Reproduction - selected-entry multi-chart certificate

Date: 2026-06-23.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi's blow-up charts repeatedly choose one entry of a finite center as a
local pivot and divide the other entries in that center by the pivot.  The
existing Lean one-chart certificate formalizes exactly one such pivot chart for
the finite center square-sum and the formal pivot-first Jacobian determinant.

This note reproduces only the finite all-pivot version of that calculation.
It is not a source proof of chart coverage, transition regularity, analytic
Jacobian control, or a global normal-crossing certificate for the DLN loss.

## Setup

Let `E` be a nonempty finite set of center labels.  For a chosen pivot
`p in E`, write the original center coordinates as

```text
x_p = u,
x_e = u y_e        for e in E \\ {p}.
```

The chart has one distinguished monomial coordinate `u`; the remaining
coordinates `y_e` are regular chart coordinates for the selected-entry finite
center calculation.

## Loss Calculation

The finite center square-sum is

```text
sum_{e in E} x_e^2.
```

In the `p`-chart it becomes

```text
u^2 + sum_{e != p} (u y_e)^2
  = u^2 (1 + sum_{e != p} y_e^2).
```

Over an ordered field, the factor

```text
1 + sum_{e != p} y_e^2
```

is nonzero, hence a unit.  The loss exponent of the single monomial
coordinate `u` is therefore `1`.

## Formal Jacobian/Prior Calculation

The formal pivot-first coordinate change has one scaling by `u` for each
non-pivot center coordinate.  Its determinant is

```text
u ^ |E \\ {p}|.
```

Thus the Jacobian/prior exponent of `u` is `|E|-1`.

## Exponent Ratio

For each pivot chart, the single active coordinate has finite ratio

```text
(|E|-1 + 1) / (2 * 1) = |E| / 2.
```

Since each pivot chart has only one active coordinate, its count at ratio
`|E|/2` is `1`.  In a finite chart family indexed by all pivots in `E`, every
chart has the same single active coordinate at the same ratio, so:

```text
exponentMinimum = |E| / 2,
minCountInChart(c) = 1 for every chart c,
exponentOrder = 1.
```

## Lean Target

The existing one-chart certificate is

```text
selectedEntryCenterSqFormalJacobianChartCertificate pivot
```

and already proves the one-pivot loss/Jacobian monomial identities and finite
exponent facts.  The next Lean target is a finite chart-family certificate
whose charts are indexed by all pivots in `E`; chart `c` should reuse the same
pivot calculation for the pivot selected by the chart index.

## Nonclaims

- No global DLN loss certificate.
- No analytic atlas coverage.
- No transition regularity between pivot charts.
- No analytic Jacobian/volume-form theorem.
- No source production of successor matrices or recurrence post-data.
- No active-ratio lower bound for a global A0 certificate.
- No pole-order theorem and no RLCT theorem.
