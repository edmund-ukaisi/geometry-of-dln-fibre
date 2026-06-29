# Reproduction - A2 Case 2 Passive Residual Finite-Mass Integrability

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean banking.  This is a
global residual-coordinate consequence for the passive chart-produced measure,
and it needs finite total passive mass.

## Question

The passive residual-coordinate pushforward theorem proves

```text
Measure.map residualMap mu
  =
passiveMeasure Set.univ •
  ((volume : Measure (center -> R)).restrict
    (CenterCoord.chartMap pivotNext '' CenterCoord.signedBoxSet Rres)).
```

where

```text
mu = Measure.map sourceChart (passiveMeasure.prod weightedBox).
```

The selected-entry chart-image measure already has residual-square positivity
almost everywhere and finite negative-power integral below the critical
threshold.  Can these facts be pulled back to `mu`?

Answer: yes, provided `passiveMeasure Set.univ < infinity`.  The scalar
`passiveMeasure Set.univ` is part of the residual marginal, so finiteness is
needed for the integral.

## Calculation

Let

```text
nu =
  (volume : Measure (center -> R)).restrict
    (CenterCoord.chartMap pivotNext '' CenterCoord.signedBoxSet Rres).
```

The selected-entry theorem gives

```text
for nu-a.e. y, 0 < aoyagiCoordinateSquareSum y

int^- y, ofReal ((aoyagiCoordinateSquareSum y)^(-t)) d nu < infinity
```

under

```text
0 <= t
forall i, 0 < Rres i
2 * t < ((center.erase (J + 2, J + 2)).card : R) + 1.
```

The residual marginal is

```text
Measure.map residualMap mu = passiveMeasure Set.univ • nu.
```

For positivity, scalar multiplication preserves a.e. truths:

```text
for (passiveMeasure Set.univ • nu)-a.e. y,
  0 < aoyagiCoordinateSquareSum y.
```

Measurability of `residualMap` lets `ae_map_iff` pull this back to `mu`.

For the integral, `lintegral_smul_measure` gives

```text
int^- y, ofReal ((square y)^(-t)) d(passiveMeasure Set.univ • nu)
  =
passiveMeasure Set.univ *
  int^- y, ofReal ((square y)^(-t)) d nu.
```

This is finite because both factors are finite: the selected-entry integral is
finite, and `passiveMeasure Set.univ < infinity` is an explicit hypothesis.
Finally, `lintegral_map` pulls the finite integral back along the measurable
residual map.

## Lean Target

```text
residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
```

## Dependency Boundary

The theorem uses the global passive residual-coordinate marginal and the
selected-entry chart-image positivity/integrability theorem.  It is not a
localized statement on an arbitrary open neighborhood `U`; localizing the
source domain would generally destroy the product residual marginal unless
additional product-shape hypotheses are supplied.

## Nonclaims

- No determinant-chart Haar pushforward.
- No raw/source Haar theorem.
- No original or external DLN source prior.
- No source-image equality or coverage.
- No local inverse or coverage theorem.
- No localization of the residual marginal through arbitrary open sets.
- No normal crossings, pole order, or RLCT.

