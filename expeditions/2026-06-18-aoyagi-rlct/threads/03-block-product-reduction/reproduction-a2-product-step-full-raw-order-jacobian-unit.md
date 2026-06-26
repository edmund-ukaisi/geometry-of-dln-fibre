# Reproduction - A2 product-step full raw-order Jacobian unit

Date: 2026-06-26.

Status: pen-and-paper determinant-order check and Lean determinant-unit
checkpoint for the full p. 13 one-step formal tangent map.

## Question

The full p. 13 formal tangent map is naturally a raw-to-chart map:

```text
(C1,D,F3old,A1,A2,A3,A4)
  -> (Ctop,D,A1,A3,F2,F3,C).
```

The domain and codomain are linearly equivalent, but their tuple orders are
not the same.  A determinant statement should therefore use the chart-output
reorder

```text
(Ctop,D,A1,A3,F2,F3,C)
  -> (Ctop,D,F3,A1,F2,A3,C),
```

so that the codomain has the same raw-shaped tuple order as the domain.

## Pen-and-Paper Check

The previous checkpoint proved a raw/chart formal tangent equivalence

```text
J : RawTangent ~= ChartTangent.
```

The chart-output reorder is a coordinate permutation

```text
P : ChartTangent ~= RawTangent.
```

Thus the determinant-facing map is the raw-order automorphism

```text
P o J : RawTangent -> RawTangent.
```

Both `J` and `P` are linear equivalences.  Their composition is a linear
equivalence of the finite raw tangent module.  Therefore its determinant is a
unit.  No entrywise determinant expansion or sign computation is needed for
unitness; the permutation determinant is itself a unit and the raw/chart
formal map is already an equivalence.

The determinant hypotheses are the determinant-chart assumptions from the
coordinate change:

```text
IsUnit C1.det
IsUnit A1.det.
```

No determinant condition on `D`, `A3`, `F3`, or `C` is used.

## Lean Target Landed

`ProductReductionStepJacobian.lean` now defines the raw-order endomorphism and
its automorphism witness:

```text
productReductionStepFormalJacobianRawOrder
productReductionStepFormalJacobianRawOrder_apply
productReductionStepFormalJacobianRawOrderEquiv
productReductionStepFormalJacobianRawOrderEquiv_apply
```

and proves the finite determinant-unit theorem:

```text
productReductionStepFormalJacobianRawOrder_det_isUnit
```

The theorem uses `[Finite pi] [Finite nu]`, in addition to the ambient
`[Fintype rho]`, `[DecidableEq rho]`, and `[Fintype mu]`, so that the full raw
tangent product module is finite for `LinearMap.det`.

## Guardrails

This proves only a finite formal determinant-unit statement for the p. 13
tangent calculation.  It does not identify the map as an analytic derivative
of the nonlinear coordinate change, does not prove a change-of-variables
formula, and does not transport source measures or densities.

It also does not prove chart coverage, normal crossings, pole order, or RLCT.
