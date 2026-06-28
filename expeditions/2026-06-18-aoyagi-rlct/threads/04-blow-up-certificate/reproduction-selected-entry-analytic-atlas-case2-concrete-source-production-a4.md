# Reproduction - Case 2 concrete selected-entry source-production payload

Date: 2026-06-28.

Status: pen-and-paper reproduction for a narrow A4 constructor theorem.

## Question

The selected-entry analytic atlas boundary has a field

```text
source_production : SourceProduction chartCertificate.
```

For the displayed continuing Case 2 lane, the current nonvacuous predicate is

```text
SelectedEntryCase2DisplayedA0SourceProduction Cnc.
```

It asks for:

- a displayed continuing Case 2 center-square/formal-Jacobian source
  certificate;
- an active coordinate in the same chart certificate `Cnc`;
- an A0 exponent-coordinate bridge from that source certificate to
  `Cnc.exponentData` at the chosen coordinate.

This note checks the concrete constructor when `Cnc` is exactly the finite
all-pivot Case 2 selected-entry chart-family certificate

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont.
```

## Source Anchors

Aoyagi PDF pp. 19-22, Case 2, gives the displayed continuing chart
calculation.  The selected residual-block center is the finite set

```text
I = case2ResidualBlockPivotEntries n S J.
```

On the displayed pivot chart at `(J+1,J+1)`, the center coordinates have the
form

```text
x_p = u,
x_i = u y_i  for i in I \ {p}.
```

The elementary consequences already reproduced in
`reproduction-case2-continuing-certificate-without-chart-family-a4.md` and
`reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`
are:

```text
sum_{i in I} x_i^2 = u^2 * (1 + sum_{i != p} y_i^2),
det(pivot-first change) = u^(|I|-1).
```

Thus the distinguished chart coordinate has loss exponent `1` and
Jacobian/prior exponent `|I|-1`.

## Concrete Certificate

The finite all-pivot certificate

```text
Cnc = case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont
```

has one coordinate in each chart.  For any chart index

```text
c : Fin Cnc.numCharts,
```

the coordinate

```text
(c, 0) : Fin Cnc.numCharts x Fin Cnc.numCoords
```

has exactly the exponent pattern required by the displayed continuing Case 2
bridge:

```text
Cnc.lossExp c 0 = 1,
Cnc.jacobianPriorExp c 0 =
  ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)).card.
```

This is the existing finite adapter

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart.
```

It supplies

```text
Case2DisplayedContinuingExponentCoordinateBridge cert Cnc.exponentData (c,0).
```

The A0 bridge wrapper contains this finite exponent bridge plus the explicit
notation that this exponent bridge is being used as A0-facing data.  In the
current Lean API the wrapper is a one-field structure, so for this concrete
`Cnc` it is constructed by setting

```text
toExponentCoordinateBridge =
  case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
    .localExponentCoordinateBridge_anyChart cert c
```

## Payload Constructor

The source-production payload is then:

```text
cert =
  sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily
    pre u residual hS hSL hcont hnext exponentPre levelInv leastValueGap C

activeCoord = (c, 0)

a0Coord =
  the A0 wrapper built from localExponentCoordinateBridge_anyChart cert c.
```

Therefore

```text
SelectedEntryCase2DisplayedA0SourceProduction Cnc
```

is inhabited for the concrete all-pivot certificate, under the same finite
continuation and recurrence/exponent hypotheses needed to build `cert`.

## What This Removes

If an analytic-atlas boundary is instantiated with this concrete chart
certificate and with `SourceProduction` equal to
`SelectedEntryCase2DisplayedA0SourceProduction`, then its `source_production`
field can be filled by construction rather than supplied as an opaque payload.

This is real but narrow: it removes only the source-production payload for this
finite all-pivot chart certificate.  It does not fill the other analytic-atlas
boundary fields.

## Guardrails

This constructor must not claim:

- analytic chart coverage;
- chart regularity, transition regularity, or unit regularity;
- analytic Jacobian or volume-form compatibility;
- global source successor, suffix, or terminal branch production;
- global active-ratio lower bounds or chart-count bounds;
- normal crossings, pole order, or RLCT extraction;
- any result for an arbitrary supplied `Cnc`.

For an arbitrary later A0 chart certificate, the coordinate and exponent
equalities remain real data unless that certificate is concretely identified
with the finite all-pivot certificate or otherwise supplies the same exponent
pattern.

## Kill Conditions

- Kill the Lean theorem if it abstracts over an arbitrary `Cnc` while proving
  the exponent coordinate by definitional equality.
- Kill the Lean theorem if it uses `SourceProductionObligation` as a
  substitute for the displayed center-square/formal-Jacobian certificate.
- Kill the Lean theorem if it fills `coverage`, `chart_regular`,
  `transition_regular`, `analytic_jacobian_compatible`, or
  `branch_termination`.
