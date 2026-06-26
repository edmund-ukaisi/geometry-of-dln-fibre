# Reproduction - A2 product-step raw-order fderiv determinant unit

Date: 2026-06-26.

Status: landed.  Lean name:
`fderiv_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit`.

## Question

The previous checkpoint proved

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder
```

for the ambient raw-order composite

```text
F z =
  productReductionStepChartTangentRawOrderEquiv
    (productReductionStepTopologyTupleToChart z).
```

Its derivative at `x.topologyTuple` is

```text
LinearMap.toContinuousLinearMap
  (productReductionStepFormalJacobianRawOrder x).
```

The formal finite determinant theorem already proves

```text
IsUnit (LinearMap.det (productReductionStepFormalJacobianRawOrder x)).
```

We want the same unit statement for the determinant of the actual Frechet
derivative `fderiv R F x.topologyTuple`.

## Pen-and-Paper Check

Let

```text
J = productReductionStepFormalJacobianRawOrder x.
```

The raw-order derivative theorem gives

```text
HasFDerivAt F (LinearMap.toContinuousLinearMap J) x.topologyTuple.
```

By uniqueness of Frechet derivatives in the ambient finite-dimensional normed
spaces,

```text
fderiv R F x.topologyTuple = LinearMap.toContinuousLinearMap J.
```

The determinant of a continuous linear map is definitionally the determinant
of its underlying linear map:

```text
(LinearMap.toContinuousLinearMap J).det = LinearMap.det J.
```

Therefore the determinant unit statement for `fderiv R F x.topologyTuple`
is exactly the already-landed finite formal theorem
`productReductionStepFormalJacobianRawOrder_det_isUnit`.

## Lean Target

Lean proves:

```text
fderiv_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
```

The proof:

1. obtains the raw-order `HasFDerivAt` theorem;
2. rewrites `fderiv` by `hf.fderiv`;
3. closes by the formal determinant theorem.

## Guardrails

This theorem proves only unitness of the determinant of the actual ambient
Frechet derivative in raw order.  It does not prove a determinant-chart subtype
derivative, a source-measure pushforward, density transport, a change-of-
variables theorem for integrals, normal crossings, pole order, or RLCT.
