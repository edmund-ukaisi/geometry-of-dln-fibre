# Reproduction - A2 signed-box residual continuous-density finite-integral bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction for a local finite-integral hypothesis
handoff.

## Source Anchor

The p.13 local finite-integral bridge has a continuous-density variant: instead
of assuming local a.e. facts

```text
0 <= density(x,u),
density(x,u) <= C,
```

on a source neighborhood and regular-coordinate ball, it assumes
`ContinuousAt density (x0,0)` and `0 < density(x0,0)`.  After shrinking the
regular-coordinate radius, those two local density bounds follow.

The previous signed-box residual source finite-integral bridge supplied the
residual positivity and residual negative-power integrability hypotheses, but
kept the local density bounds explicit.  This slice composes the signed-box
residual source constructor with the continuous-density finite-integral bridge.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

and

```text
res(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge x).
```

The weighted signed-box source theorem assumes a chart and source density with

```text
mu.restrict S =
  Measure.map sourceChart
    (signedBox.withDensity (ofReal sourceDensity)).
```

Together with fixed-basis edge-matrix measurability, residual lower bound,
source-density a.e.-measurability, source-density a.e. nonnegativity, and the
source-density monomial upper bound, it proves

```text
forall^ae x with respect to mu.restrict S, 0 < res(x)
```

and

```text
int^-_x ofReal(res(x)^(-t)) d(mu.restrict S) < infinity.
```

The signed-box residual theorem needs `t >= 0`; the composed local finite-side
theorem assumes `0 < t`, so this is supplied by `0 < t`.

The existing continuous-density p.13 theorem then consumes these residual
source hypotheses, plus:

```text
MeasurableSet S,
0 < Rmax,
0 < creg,
ContinuousAt density (x0,0),
0 < density(x0,0),
creg * (res(x) + squareSum(u)) <= loss(x,u)
```

on the source-neighborhood and regular-coordinate ball of radius `Rmax`.

It shrinks the regular-coordinate radius to some `R <= Rmax`, produces a
bound `C` for the density, shrinks the source neighborhood to an open `U`,
and concludes finiteness of

```text
int^- ofReal(loss(x,u)^(-(t + regularCount/2)) * density(x,u))
```

over `(mu.restrict (U inter S)).prod nu`, with indicator support on the ball
of radius `R`.

## Boundaries

This is only composition of already-proved residual-source and
continuous-density local-measure plumbing.  It still assumes source-stratum
measurability, fixed-basis edge-matrix measurability, the signed-box chart,
the weighted source pushforward identity, the residual monomial lower bound,
source-density measurability/nonnegativity/upper bound, product-density
continuity and positivity at the chart center, and the regular-fiber loss lower
bound.

It does not construct Aoyagi's analytic chart, prove the pushforward identity,
transport Jacobian or prior density, compare with the original
DLN/statistical loss, produce normal crossings, compute pole order, or extract
an RLCT.

## Kill Conditions

- Do not treat continuity and positivity of `density` at `(x0,0)` as proving
  the density/Jacobian transport theorem; the density itself remains supplied.
- Do not treat this as proving residual positivity or integrability without
  the signed-box chart and monomial hypotheses.
- Do not use this theorem as an original-loss comparison or product-chart
  construction theorem.
