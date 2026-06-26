# Reproduction - A2 product-step weighted Haar change of variables

Date: 2026-06-26.

Status: landed. Lean names:

```text
ProductReductionStepRawTopologyTuple
productReductionStepRawDetChartSet
isOpen_productReductionStepRawDetChartSet
nullMeasurableSet_productReductionStepRawDetChartSet
productReductionStepTopologyTupleToChartRawOrder
productReductionStepRawOrderJacobianCLM
productReductionStepRawOrderJacobianAbsDet
map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det
```

## Question

Mathlib's finite-dimensional Jacobian theorem gives a weighted pushforward
identity for an injective differentiable map on a null-measurable set.  After
the product-step derivative and injectivity checkpoints, the remaining task is
to package the raw-order p. 13 product-step map in that API.

## Pen-and-Paper Check

Let

```text
E = (C1,D,G,A1,A2,A3,A4)
```

be the raw tuple space over the real finite matrix coordinates, and let

```text
S = {z in E | det(C1) and det(A1) are units}.
```

The raw-order p. 13 coordinate map is

```text
Ctop = C1 A1
D    = D
F3   = G - D A3 (C1 A1)^(-1)
A1   = A1
F2   = -A1^(-1) A2
A3   = A3
C    = A4 - A3 A1^(-1) A2.
```

The determinant chart is open because it is the intersection of the two
determinant-unit preimages for `C1` and `A1`.  The landed derivative theorem
states that, on `S`, the Frechet derivative within `S` is the continuous-linear
map obtained from the formal raw-order Jacobian.  The landed injectivity
theorem states that the same raw-order map is injective on `S`.

Thus the three hypotheses of Mathlib's theorem are available:

```text
NullMeasurableSet S m
forall z in S, HasFDerivWithinAt Phi (J z) S z
Set.InjOn Phi S
```

for any additive Haar measure `m` on the raw tuple space.  Mathlib then gives

```text
map Phi ((m.restrict S).withDensity (fun z => ofReal |det(J z)|))
  = m.restrict (Phi '' S).
```

The Lean statement keeps `NullMeasurableSet S m` explicit, and also proves a
separate convenience lemma deriving it from openness under a Borel-space
measurable structure.

## Guardrails

This is weighted additive-Haar transport to the image of the raw determinant
chart. It does not identify that image with the whole target determinant
chart, does not transport the original DLN source/prior measure, does not
prove source coverage, does not produce normal crossings, and does not compute
an RLCT or pole order.

The theorem uses `[Fintype pi] [Fintype nu]` rather than only `[Finite pi]
[Finite nu]` because Mathlib's normed matrix instances for the Jacobian
theorem need actual finite-type instances at the theorem boundary.
