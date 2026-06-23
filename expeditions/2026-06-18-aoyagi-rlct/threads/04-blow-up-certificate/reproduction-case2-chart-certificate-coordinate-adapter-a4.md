# Reproduction - Case 2 chart-certificate coordinate adapter

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-chart-certificate-coordinate-adapter-a4.md`.

## Source Anchor

Aoyagi PDF pp. 5-6 gives the finite normal-crossing ratio from a chart
coordinate by reading two exponent arrays: the loss exponent and the
Jacobian/prior exponent.  The existing A0 chart-certificate spine records
those arrays on `AoyagiNormalCrossingChartCertificate` and projects them
definitionally to `Cnc.exponentData`.

The Case 2 local arithmetic from PDF pp. 19-22 has already been isolated in
the displayed continuing finite certificate: at the displayed selected-entry
coordinate, the loss exponent is `1`, and the formal pivot-first
Jacobian/prior exponent is

```text
card ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).
```

This slice does not assert that Aoyagi constructs the global chart
certificate.  It only adapts already-supplied equalities stated on a supplied
chart certificate `Cnc` to the older bridge whose input is
`Cnc.exponentData`.

## Pen-and-Paper Calculation

Let `Cnc` be a supplied `AoyagiNormalCrossingChartCertificate`, and let

```text
p : Fin Cnc.numCharts x Fin Cnc.numCoords.
```

Assume the two coordinate exponent equalities are supplied at chart-certificate
level:

```text
Cnc.lossExp p.1 p.2 = 1,
Cnc.jacobianPriorExp p.1 p.2
  = card ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).
```

By definition of the projection `Cnc.exponentData`,

```text
Cnc.exponentData.lossExp p.1 p.2 = Cnc.lossExp p.1 p.2,
Cnc.exponentData.jacobianPriorExp p.1 p.2
  = Cnc.jacobianPriorExp p.1 p.2.
```

Therefore the same two equalities satisfy the fields of
`Case2DisplayedContinuingA0ExponentCoordinateBridge cert Cnc.exponentData p`.
All ratio/minimum consequences remain those of the existing bridge.

## Lean Target

New Lean name:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents
```

The theorem constructs:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge cert Cnc.exponentData p
```

from the two supplied equalities on `Cnc.lossExp` and
`Cnc.jacobianPriorExp`.

## Recovery Scout Boundary

The crash-recovered scout round gives the reason this slice stays small:

- A4 selected-entry atlas/coverage remains blocked; the source supports local
  finite algebra and supplied-boundary consumers, not global chart production.
- A0 chart coverage remains supplied; the selected-entry microcertificate is
  local and finite, not the full DLN loss chart family.
- A2/A3 work remains blocked by source-boundary and policy issues.

The adapter is useful because downstream chart-final sockets naturally expose
`Cnc.lossExp` and `Cnc.jacobianPriorExp`, while the existing Case 2 bridge
expects `Cnc.exponentData`.

## Boundary

This slice proves no chart certificate, no coordinate existence, no global
active-ratio lower bound, no chart-count theorem, no chart coverage, no
transition regularity, no analytic Jacobian/volume-form theorem, no normal
crossings for the DLN loss, no pole order, and no RLCT extraction.
