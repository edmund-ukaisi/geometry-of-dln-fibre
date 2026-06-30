# A2 selected-entry one-chart regular data

## Scope

This note records the one-chart chart/transition/unit regularity data supported
by the finite selected-entry substitution

```text
x_p = u,
x_i = u r_i  for i != p.
```

The chart-point coordinates are `(u, r)`.  This is one-chart regularity data
for the same `selectedEntryOneChartAnalyticAtlasContext` used by the
Jacobian/volume record.  It is not source coverage, not a full analytic atlas
producer, not source production, and not an RLCT extraction theorem.

## Chart Regularity

The exposed one-chart map is:

```text
formalChartMap_p(u, r)_p = u,
formalChartMap_p(u, r)_i = u r_i  for i != p.
```

Each component is continuous: the pivot component is first projection, and
each non-pivot component is the product of first projection with one residual
projection.  Lean already proves this as:

```text
continuous_formalChartMap
```

The certificate coordinate is the pivot coordinate:

```text
coord_0(u, r) = u.
```

Thus the chart map and the unique certificate coordinate are continuous on the
universal chart domain.

## Transition Regularity

For this one-chart context there is only one chart.  The transition domain is
`univ`, and the transition map is the identity map on chart-point coordinates.
It is continuous, lands in the universal chart domain, and preserves the chart
map by reflexivity.

This is one-chart identity-transition data only.  It does not construct
overlap maps between different selected pivots or prove analytic transition
regularity for a finite covering atlas.

## Unit Regularity

The selected-entry loss unit is:

```text
lossUnit(u, r) = 1 + sum_{i != p} r_i^2.
```

This is continuous as a finite sum of squares of residual coordinate
projections.  It is a unit because it is strictly positive over `ℝ`, already
proved by the finite certificate.

The Jacobian/prior unit is constant:

```text
jacobianPriorUnit(u, r) = 1.
```

It is continuous and a unit.

## Lean names

The helper continuity lemmas are:

```text
continuous_chartPointCoord
continuous_chartPointLossUnit
continuous_chartPointJacobianPriorUnit
```

The one-chart data records are:

```text
selectedEntryOneChartAnalyticChartRegularData
selectedEntryOneChartAnalyticTransitionRegularData
selectedEntryOneChartAnalyticUnitRegularData
```

## Kill Conditions

- Kill if this is described as source coverage or a full analytic atlas
  producer.
- Kill if this is described as transition regularity for multiple selected
  pivots or a chart family.
- Kill if this is used to claim source production, branch termination,
  normal-crossing extraction, pole order, or RLCT.
- Kill if it is used as source-prior transport, determinant-chart Haar
  transport, or source-rank coverage.
