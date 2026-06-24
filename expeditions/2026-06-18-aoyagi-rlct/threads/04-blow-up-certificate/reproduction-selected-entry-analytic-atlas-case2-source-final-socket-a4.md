# Reproduction - Selected-entry analytic atlas Case 2 source final socket

Date: 2026-06-24.

Status: pen-and-paper reproduction for a narrow A4 consumer theorem.

## Question

The selected-entry analytic atlas boundary now carries a supplied
`AoyagiNormalCrossingChartCertificate` plus abstract fields for coverage,
regularity, transition regularity, unit control, analytic Jacobian
compatibility, source production, and branch termination.  The existing final
adapter can project this certificate to the A0/A6 chart-final socket only when
the finite Theorem 2 exponent formula is supplied directly.

The next useful question is whether a nontrivial source-production predicate
can feed the existing displayed Case 2/A0 finite-exponent bridge, rather than
treating the finite exponent formula as an opaque input.

## Source Anchors

Aoyagi PDF pp. 19-22 gives the displayed continuing Case 2 chart calculation.
The chosen residual-block pivot is the displayed pair `(J+1,J+1)`, the
selected residual block is rewritten in selected-entry coordinates, and the
center-square contribution has the normal form

```text
u^2 * unit.
```

The pivot-first selected-entry determinant contributes the formal power

```text
u^(|I|-1),
```

where `I` is the residual-block center.  The source calculation therefore
produces one displayed coordinate with finite exponents

```text
loss exponent = 1,
Jacobian/prior exponent = |I|-1.
```

Aoyagi PDF pp. 5-6 is the normal-crossing extraction display.  In this
project, only the normal-crossing-to-RLCT extraction theorem is allowed as a
citation boundary.  The present slice does not invoke it except through an
explicit chart-level `ExtractionHypothesis`.

## Elementary Calculation

Let

```text
I = case2ResidualBlockPivotEntries n S J.
```

On the selected-entry pivot chart, write

```text
z_p = u,
z_i = u y_i  for i != p.
```

Then

```text
sum_i z_i^2 = u^2 * (1 + sum_{i != p} y_i^2).
```

The finite exponent attached to the loss is therefore `k=1`.  The pivot-first
coordinate change has formal determinant

```text
u^(|I|-1),
```

so the Jacobian/prior exponent is `h=|I|-1`.  The displayed coordinate has
ratio

```text
(h+1)/(2k) = |I|/2.
```

This is the exact finite calculation already expressed by
`Case2DisplayedContinuingA0ExponentCoordinateBridge`: it records the coordinate
as active and identifies its ratio with half the residual-block center
cardinality.

## Final-socket Inputs That Must Remain Explicit

This calculation still does not determine the final Theorem 2 boundary by
itself.  A chart-final handoff also needs:

- selected-width provenance `m = aoyagiSelectedReducedWidths H r cuts`;
- the chart-level extraction hypothesis for the supplied chart certificate;
- the equality between the displayed center-card ratio and the Theorem 2
  lambda formula from Definition 3 ceiling data;
- a global lower bound saying every active coordinate ratio in the supplied
  exponent data is at least the displayed ratio;
- a chart count realizing the displayed pole-order formula;
- an upper bound showing no chart has a larger count at the displayed ratio.

These are exactly the explicit hypotheses of the existing
`Case2DisplayedContinuingA0ExponentCoordinateBridge` chart-final bridge.

## Nontrivial Source-production Predicate

The source-production field of `SelectedEntryAnalyticAtlasBoundary` should not
be instantiated by `True`, by a finite selected-entry certificate alone, or by
a formula-level `SourceProductionObligation` wrapper.  For this slice it should
instead carry concrete data:

```text
cert : displayed continuing Case 2 source-chart center-square/formal-Jacobian
       certificate
activeCoord : coordinate in the supplied A0 chart certificate
a0Coord : Case2DisplayedContinuingA0ExponentCoordinateBridge cert
          Cnc.exponentData activeCoord
```

This is still supplied source-production data, not a proof that the analytic
atlas produces it.  But it is not vacuous: it ties the source-production field
to an actual displayed Case 2 source calculation and to a coordinate of the
same chart certificate consumed by the final socket.

## Target Lean Statement

Define a data structure for the displayed Case 2/A0 source-production payload
and a propositional predicate saying such data is nonempty.  Then prove a
theorem in the `SelectedEntryAnalyticAtlasBoundary` namespace:

```text
if B.source_production carries a displayed Case 2 source certificate plus an
A0 exponent-coordinate bridge for B.chartCertificate.exponentData, and if the
selected-width, extraction, lambda, active-ratio, and chart-count hypotheses
are supplied, then B.chartCertificate satisfies
AoyagiTheorem2SuppliedChartFinalBoundary.
```

The proof is pure composition: unwrap the source-production payload and call
the existing displayed Case 2/A0 chart-final bridge.

## Guardrails

This slice must not:

- construct an analytic atlas;
- prove chart coverage;
- prove chart or transition regularity;
- prove analytic Jacobian or volume-form compatibility;
- prove source successor, suffix, or terminal production;
- prove normal crossings, pole order, or RLCT;
- infer global active-ratio or chart-count facts from the local selected-entry
  coordinate.
