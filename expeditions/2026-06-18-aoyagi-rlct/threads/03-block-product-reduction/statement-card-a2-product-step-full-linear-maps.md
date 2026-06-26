# Statement Card - A2 product-step full formal linear maps

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

The full p. 13 one-step formal tangent formulas are bundled as Lean
`LinearMap`s at fixed raw and chart base points, and the bundled maps apply to
the previously recorded formula functions.

## Lean Names

```text
productReductionStepFormalJacobian
productReductionStepFormalJacobian_apply
productReductionStepFormalJacobianInverse
productReductionStepFormalJacobianInverse_apply
```

Supporting component/projection names include
`productReductionStepRawTangent_dC1`, `productReductionStepRawTangent_dD`,
`productReductionStepRawTangent_dF3old`, `productReductionStepRawTangent_dA1`,
`productReductionStepRawTangent_dA2`, `productReductionStepRawTangent_dA3`,
`productReductionStepRawTangent_dA4`,
`productReductionStepChartTangent_dCtop`, `productReductionStepChartTangent_dD`,
`productReductionStepChartTangent_dA1`, `productReductionStepChartTangent_dA3`,
`productReductionStepChartTangent_dF2`, `productReductionStepChartTangent_dF3`,
and `productReductionStepChartTangent_dC`.

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- raw or chart coordinate base point.

No determinant theorem is stated in this slice, so no finite `pi`/`nu`
determinant assumptions are introduced here.

## Not Proved

The full forward and inverse maps are not yet assembled into a `LinearEquiv`,
and no determinant-unit theorem is claimed. The next frontier is to prove the
two inverse-composition identities, then compose the forward map with
`productReductionStepChartTangentRawOrderEquiv` before stating any determinant
result.

No analytic derivative, source-measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Verified on 2026-06-26 with the focused module build passing.
