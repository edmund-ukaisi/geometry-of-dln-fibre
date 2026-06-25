# Reproduction - A2 signed-box residual source finite-integral bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction for a local finite-integral hypothesis
handoff.

## Source Anchor

The p.13 local finite-integral bridge consumes three source-side inputs on the
source-rank stratum:

```text
source-stratum measurability,
residual square-sum positivity a.e.,
finite residual negative-power integral.
```

The weighted signed-box residual source constructor already proves the last
two inputs from a supplied chart pushforward, a monomial residual lower bound,
and a monomial density upper bound.  This slice composes those two pieces so
the p.13 local finite-integral theorem can be applied directly from the
signed-box residual source data.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

and let

```text
res(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge x).
```

The existing weighted signed-box source theorem assumes a chart

```text
chart : (i -> R) -> alpha
```

and a signed-box density `sourceDensity`, with

```text
mu.restrict S =
  Measure.map chart (signedBox.withDensity (ofReal sourceDensity)).
```

It also assumes the chart-side bounds

```text
c_res * prod_i |y_i|^(2*k_i) <= res(chart y),
0 <= sourceDensity(y),
sourceDensity(y) <= C_res * prod_i |y_i|^(h_i),
2*t*k_i < h_i + 1.
```

Under `t >= 0`, the signed-box source constructor proves

```text
forall^ae x with respect to mu.restrict S, 0 < res(x)
```

and

```text
int^-_x ofReal(res(x)^(-t)) d(mu.restrict S) < infinity.
```

The composed p.13 finite-integral bridge assumes the stronger `0 < t`, so the
residual-source constructor is applied with `t >= 0` obtained from `0 < t`.
The existing p.13 finite-integral theorem then takes these two residual source
hypotheses, plus the source-stratum measurability and the local
regular-fiber loss/density bounds

```text
c_reg * (res(x) + squareSum(u)) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= C_reg
```

on a source-neighborhood and regular-coordinate ball.  It shrinks the source
neighborhood and concludes finiteness of

```text
int^- ofReal(loss(x,u)^(-(t + regularCount/2)) * density(x,u))
```

over the restricted source set times the regular-coordinate Haar measure.

Therefore the signed-box residual-source theorem can be used as a direct
front-end for the p.13 local finite-integral bridge.

## Boundaries

This is only measure/integrability plumbing.  It still assumes the signed-box
chart, the source-measure pushforward identity, the signed-box residual lower
bound, the signed-box density bounds, source-stratum measurability, and the
local regular-fiber loss/density bounds.  It does not construct Aoyagi's
analytic chart, prove the pushforward identity, transport Jacobian or prior
density, compare with the original DLN/statistical loss, produce normal
crossings, compute pole order, or extract an RLCT.

## Kill Conditions

- Do not treat this as proving residual positivity or integrability without
  the signed-box chart and monomial hypotheses.
- Do not treat the regular-fiber loss/density bounds as consequences of this
  theorem; they remain explicit inputs.
- Do not use this theorem to replace chart construction, source-measure
  transport, or Jacobian/prior-density transport.
