# Reproduction - A2 suffix-step raw-order inverse density handoff

Date: 2026-06-26.

Status: in progress.  Lean target:

```text
ProductReductionStepSuffixDensity.lean
```

## Question

The left-endpoint p. 13 density handoff used a concrete target tuple.  The
generic product-reduction recursion already has one-step raw coordinates
attached to an arbitrary suffix state:

```text
x = stepRawCoordinates E p S F3prev.
```

The next elementary bridge is to feed this arbitrary one-step tuple through the
same raw-order product-step chart map and prove that the resulting raw-shaped
target tuple lies in the target determinant chart and can be used with the
chart-side inverse Jacobian density.

## Pen-and-Paper Check

Let

```text
M = transformedEdge(E,p,S).
```

Write the raw one-step tuple as

```text
x = (C1,D,F3old,A1,A2,A3,A4)
  = (S.Ctop, S.D, F3prev,
     topLeftCorner(M), upperRightBlock(M),
     lowerLeftBlock(M), lowerRightBlock(M)).
```

The determinant-chart hypotheses are exactly

```text
IsUnit det(S.Ctop),
IsUnit det(A1).
```

The p. 13 one-step chart formulas give

```text
Ctop = C1 A1,
D    = D,
F3   = F3old - D A3 (C1 A1)^(-1),
A1   = A1,
F2   = -A1^(-1) A2,
A3   = A3,
C    = A4 - A3 A1^(-1) A2.
```

Thus the raw-shaped target tuple is

```text
Y =
(S.Ctop A1, S.D,
 F3prev - S.D A3 (S.Ctop A1)^(-1),
 A1, -A1^(-1) A2, A3, A4 - A3 A1^(-1) A2).
```

The formulas invert `A1` and the product `S.Ctop A1`; the determinant-unit
hypothesis on `S.Ctop` makes the product a unit.  The block `D = S.D` is
passive and may be singular.

The chart-side inverse map sends a raw-shaped target tuple

```text
(Ctop,D,F3,A1,F2,A3,C)
```

to the raw source tuple

```text
(Ctop A1^(-1), D, F3 + D A3 Ctop^(-1),
 A1, -A1 F2, A3, C - A3 F2).
```

Substituting the displayed `Y` gives

```text
Ctop A1^(-1) = (S.Ctop A1) A1^(-1) = S.Ctop,
F3 + D A3 Ctop^(-1)
  = F3prev - S.D A3 (S.Ctop A1)^(-1)
      + S.D A3 (S.Ctop A1)^(-1)
  = F3prev,
-A1 F2 = -A1 (-A1^(-1) A2) = A2,
C - A3 F2
  = A4 - A3 A1^(-1) A2 - A3 (-A1^(-1) A2)
  = A4.
```

The inverse therefore recovers `x`.  This is the same coordinate change as the
raw product-step chart; no source chart, signed-box model, or prior measure is
introduced.

## Determinant Chart

In Lean, the target tuple is defined as

```text
chartLocalSuffixStateStepRawOrderTargetTuple E p S F3prev
  = productReductionStepTopologyTupleToChartRawOrder
      ((stepRawCoordinates E p S F3prev).topologyTuple).
```

The raw tuple lies in the source determinant chart by
`ChartLocalSuffixState.stepRawCoordinates_detChart`.  The existing theorem
`mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart` then moves
it to the raw-shaped target determinant chart.

## Continuity

The raw step tuple is fieldwise continuous from:

- continuity of the input edge `E p`;
- continuity of the suffix-state fields `S.B`, `S.Ctop`, and `S.D`;
- continuity of the chosen previous lower-left field `F3prev`;
- continuity of the four block projections of `transformedEdge(E,p,S)`.

At a determinant-chart basepoint, the ambient raw-order chart map is
continuous because the landed Frechet derivative theorem applies there.
Composing these two facts gives continuity of `Y`.  Composing `Y` with
`productReductionStepRawOrderInverseJacobianDensity` gives the density
continuity handoff; determinant-chart membership gives positivity.

## Kill Conditions

- If determinant-chart membership required `det(S.D)` to be a unit, the claim
  would be wrong.  The determinant chart checks only `S.Ctop` and `A1`.
- If the target tuple were interpreted as a source chart or signed-box
  parametrisation, the claim would overstate the result.
- If the continuity theorem inverted `D`, it would not match the product-step
  formulas.

## Guardrails

This is an arbitrary product-step target-tuple and reciprocal-density handoff.
It does not prove original DLN source/prior transport, source coverage,
signed-box density identification, an unweighted pushforward theorem, normal
crossings, pole order, or RLCT.
