# Reproduction - A2 Retained-Passive Signed-Box Local-Measure Handoff

Date: 2026-06-26.

Status: reproduced and formalised in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

## Target

The retained-passive local-measure handoff still assumes residual positivity
and residual negative-power integrability on

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource.
```

Existing infrastructure already derives those residual source hypotheses from
a weighted signed-box source chart, provided the source-measure pushforward and
monomial residual/density bounds are supplied.  The target is to specialize
that residual-source constructor to the retained-passive local source.

## Reproduction

Let

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Assume global `Continuous Cedge`.  The fixed-base edge-matrix map is then
continuous, hence measurable:

```text
x |-> paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0 (Cedge x)
```

This is the measurable edge-matrix input required by the existing signed-box
residual-source constructor.

Assume a signed-box chart and weighted pushforward identity

```text
mu.restrict localSource =
  Measure.map sourceChart
    ((signedBox).withDensity (fun y => ENNReal.ofReal (sourceDensity y))).
```

Together with the chart-side monomial residual lower bound and density bounds,
the existing theorem

```text
residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
```

gives residual positivity and `residualNegPowerIntegrableOn` on
`localSource`.  Feeding these into the retained-passive local-measure handoff
proves the finite p.13 regular-coordinate integral over a shrunk open
neighborhood inside the source-rank stratum.

## Boundary

This theorem does not prove the signed-box chart, the pushforward identity, or
the monomial residual/density estimates.  It only composes those supplied
facts with the retained-passive local-source coverage, measurability, and
edge-matrix measurability.  It does not construct a Jacobian density, compare
an original DLN loss, prove normal crossings, determine a pole order, or
extract an RLCT.
