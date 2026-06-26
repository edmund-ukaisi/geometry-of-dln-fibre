# Review - A2 product-step raw-order ambient derivative

Date: 2026-06-26.

Reviewers: controller.

## Verdict

Pass for the raw-order derivative bridge.  The theorem composes the full
ambient derivative with a fixed linear coordinate reorder and obtains the same
raw-order formal Jacobian endomorphism used by the determinant-unit theorem.
It does not claim measure transport or RLCT.

## Mathematical Check

The full ambient derivative is

```text
productReductionStepFormalJacobian x :
  RawTangent -> ChartTangent.
```

The reorder equivalence is

```text
productReductionStepChartTangentRawOrderEquiv :
  ChartTangent ~= RawTangent.
```

Because the reorder is linear, the derivative of the composite is the
composition

```text
productReductionStepChartTangentRawOrderEquiv.toLinearMap
  o productReductionStepFormalJacobian x,
```

which is definitionally the existing
`productReductionStepFormalJacobianRawOrder x`.

## Lean/API Check

The proof wraps the reorder equivalence as a continuous linear map, uses its
`hasFDerivAt`, and composes it with
`hasFDerivAt_productReductionStepTopologyTupleToChart`.  The final `simpa`
unfolds `productReductionStepFormalJacobianRawOrder`, so the target is the
same raw-order endomorphism whose determinant unitness is already landed.

## Scope Check

This bridge reaches the determinant-facing derivative map in ambient vector
coordinates.  The remaining boundary is turning this into the actual analytic
change-of-variables/source-measure transport needed for the Aoyagi RLCT
argument, or fitting it into the normal-crossing chart certificate.  Those
steps remain open.
