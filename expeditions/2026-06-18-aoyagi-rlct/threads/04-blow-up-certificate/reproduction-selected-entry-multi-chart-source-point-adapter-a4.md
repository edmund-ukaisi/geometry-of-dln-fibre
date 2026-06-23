# Reproduction - selected-entry multi-chart source-point adapter

Date: 2026-06-23.

Status: reproduced before Lean implementation.

## Setup

Let `E` be a nonempty finite center and let

```text
chartEquiv : Fin |E| ~= E
```

index all pivot charts.  For a chart index `c`, write

```text
p = chartEquiv(c).
```

The all-pivot certificate is defined chartwise: chart `c` is exactly the
existing one-pivot selected-entry microcertificate at pivot `p`.

## Source Point

Given an ambient residual assignment `residual : iota -> K` and a pivot
coordinate `u`, the source point in chart `c` is the one-pivot source point

```text
(u, residual restricted to E \ {p}).
```

Thus the chart map evaluates to

```text
x_p = u,
x_e = u residual_e     for e in E \ {p}.
```

Equivalently, as a function on the center subtype,

```text
chartMap(c, sourcePoint(c,u,residual))(i)
  = selectedEntryChartMap p u residual i.
```

## Loss And Unit

Because chart `c` is definitionally the one-pivot certificate at `p`, the
finite loss at this source point is

```text
sum_{i in E} selectedEntryChartMap(p,u,residual)_i^2.
```

The recorded loss unit is the normalized selected-entry square factor

```text
1 + sum_{e in E \ {p}} residual_e^2.
```

The already-proved one-pivot calculation shows the monomial identity

```text
loss(chartMap(c, sourcePoint)) =
  lossUnit(c, sourcePoint) * u^2.
```

## Formal Jacobian/Prior

The recorded formal Jacobian/prior in chart `c` is

```text
u ^ |E \ {p}|.
```

Equivalently it is the determinant of the pivot-first formal matrix

```text
[ 1  0 ]
[ y  uI].
```

The already-proved one-pivot calculation gives the monomial identity

```text
jacobianPrior(c, sourcePoint) =
  jacobianPriorUnit(c, sourcePoint) * u ^ |E \ {p}|.
```

## Lean Target

Add source-point adapters under
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate` which delegate each
chart `c` to the one-pivot source-point lemmas for `chartEquiv c`.

The target is presentation only: it should not change the chart family or
exponent data.

## Nonclaims

- No analytic atlas coverage.
- No transition regularity between pivot charts.
- No analytic Jacobian/volume-form theorem.
- No source production of successor matrices or recurrence post-data.
- No global DLN loss certificate.
- No active-ratio lower bound for a global A0 certificate.
- No pole-order theorem and no RLCT theorem.
