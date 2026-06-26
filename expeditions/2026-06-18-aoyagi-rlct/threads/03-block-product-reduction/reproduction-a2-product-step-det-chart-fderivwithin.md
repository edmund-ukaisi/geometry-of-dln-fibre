# Reproduction - A2 product-step determinant-chart `fderivWithin`

Date: 2026-06-26.

Status: landed. Lean names:

```text
isOpen_productReductionStepRawTopologyTuple_detChart
hasFDerivWithinAt_productReductionStepTopologyTupleToChart_rawOrder_detChart
fderivWithin_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
```

## Question

The previous checkpoint proved unitness of the determinant of the ambient
Frechet derivative of the raw-order p. 13 one-step coordinate map. The next
change-of-variables interface wants the derivative on the determinant-chart
domain, i.e. the open set

```text
S = {z | IsUnit z.C1.det and IsUnit z.A1.det}.
```

We need the `fderivWithin` determinant unit statement on `S`, without claiming
a derivative on the subtype `{z // z in S}`.

## Pen-and-Paper Check

Let

```text
F z =
  productReductionStepChartTangentRawOrderEquiv
    (productReductionStepTopologyTupleToChart z).
```

The raw determinant-chart set is

```text
S = {z | IsUnit z.1.det and IsUnit z.2.2.2.1.det}.
```

The coordinate projections `z -> z.1` and `z -> z.2.2.2.1` are continuous
maps from the ambient product space to square real matrix spaces. The
determinant is continuous, and the unit locus in `R` is open. Therefore each
condition

```text
IsUnit z.1.det
IsUnit z.2.2.2.1.det
```

defines an open subset, and their intersection `S` is open.

At a raw coordinate point `x` with `IsUnit x.C1.det` and `IsUnit x.A1.det`, we
have `x.topologyTuple in S`. The landed ambient theorem gives

```text
HasFDerivAt F (LinearMap.toContinuousLinearMap J) x.topologyTuple
```

for

```text
J = productReductionStepFormalJacobianRawOrder x.
```

Restricting an ambient derivative to any domain gives

```text
HasFDerivWithinAt F (LinearMap.toContinuousLinearMap J) S x.topologyTuple.
```

Since `S` is open and contains `x.topologyTuple`,

```text
fderivWithin R F S x.topologyTuple = fderiv R F x.topologyTuple.
```

Thus the determinant-unit statement for `fderivWithin` is exactly the previous
ambient determinant-unit theorem.

## Guardrails

This closes only the ambient open-domain derivative boundary. It does not
prove differentiability as a map between determinant-chart subtypes, injective
local change of variables for measures, a pushforward density formula, source
coverage, normal crossings, pole order, or RLCT.
