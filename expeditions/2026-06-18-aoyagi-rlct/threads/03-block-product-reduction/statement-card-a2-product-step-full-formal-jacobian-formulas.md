# Statement Card - A2 product-step full formal Jacobian formulas

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

The full p. 13 one-step formal tangent formulas are now recorded in Lean for
all raw variables `(C1,D,F3old,A1,A2,A3,A4)`, and the chart tangent output has
an explicit reorder equivalence into raw-shaped order.

## Lean Names

```text
ProductReductionStepRawTangent
ProductReductionStepChartTangent
productReductionStepFormalJacobianFormula
productReductionStepFormalJacobianInverseFormula
productReductionStepChartTangentRawOrderEquiv
```

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- raw or chart coordinate base point.

No determinant theorem is stated in this slice, so no finite `pi`/`nu`
determinant assumptions are introduced here.

## Not Proved

The full formulas are not yet bundled as `LinearMap`s or a `LinearEquiv`, and
no full determinant-unit theorem is claimed.  The theorem frontier is to prove
linearity/inverse composition in smaller components and then compose the
forward map with `productReductionStepChartTangentRawOrderEquiv` before taking
a determinant.

No analytic derivative, source-measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Verified on 2026-06-26 with the focused module build passing cleanly.
