# Reproduction - A2 p.13 raw product-step preimage

Date: 2026-06-26.

Status: Lean target selected.

## Question

The raw product-step inverse-density pushforward is a theorem about the
abstract one-step raw coordinate map.  To use it in the p. 13 regular-coordinate
family, we need the source-side raw tuple whose product-step image is the
already-defined p. 13 raw-shaped target tuple

```text
Y(x,u) = (Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

This is still only a raw product-chart construction.  It does not identify an
original DLN source measure, prove source coverage, or compare with the full
loss.

## Pen-and-Paper Check

For the raw-order product-step map,

```text
Phi(C1,D,F3old,A1,A2,A3,A4)
  =
  (C1*A1,
   D,
   F3old - D*A3*(C1*A1)^(-1),
   A1,
   -A1^(-1)*A2,
   A3,
   A4 - A3*A1^(-1)*A2).
```

Set

```text
X(x,u) = (I, Dtail(x), F3(u), Ctop(u), -Ctop(u)*F2(u), 0, C0(x)).
```

If `det Ctop(u)` is nonzero, then `X(x,u)` is in the raw determinant chart:
the two determinant-chart blocks are `I` and `Ctop(u)`.

Substituting `X` into `Phi` gives:

```text
C1*A1 = I*Ctop = Ctop,
D = Dtail,
F3old - D*A3*(C1*A1)^(-1) = F3 - Dtail*0*Ctop^(-1) = F3,
A1 = Ctop,
-A1^(-1)*A2 = -Ctop^(-1)*(-Ctop*F2) = F2,
A3 = 0,
A4 - A3*A1^(-1)*A2 = C0 - 0 = C0.
```

Thus

```text
Phi(X(x,u)) = Y(x,u).
```

At the centered regular-coordinate point, `Ctop(0) = I`, so the determinant
condition holds automatically.

## Lean Shape

Add to `ProductReductionStepRegularDensity.lean`:

```text
paperEndpointFixedBaseP13RawPreimageTuple
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center
productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
```

The last theorem should state that applying
`productReductionStepTopologyTupleToChartRawOrder` to the preimage tuple gives
`paperEndpointFixedBaseP13RawOrderTuple`, under the determinant-unit hypothesis
on `Ctop(u)`.

## Kill Conditions

- If the proof needs any inverse of `Dtail`, the statement is wrong.
- If it claims source coverage or a source-measure pushforward, it overclaims.
- If it uses original DLN coordinates rather than the p. 13 raw product chart,
  split the target; this slice is only the one-step raw preimage calculation.

## Nonclaims

No original DLN source/prior transport, no signed-box density identification,
no p.13 source coverage, no regular-suspension certificate, no normal
crossings, no pole order, and no RLCT.
